/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Kroening, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Runs system commands. Won't work for windows
 */

#include "run.h"
#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>

#include "base/check.h"
#include "signal_catcher.h"

namespace cvc5 {

int run(const std::string& what, const std::vector<std::string>& argv)
{
  return run(what, argv, "", "", "");
}

using fdt = int;

/// open given file to replace either stdin, stderr, stdout
static fdt stdio_redirection(int fd, const std::string& file)
{
  if (file.empty()) return fd;

  int flags = 0, mode = 0;
  std::string name;

  switch (fd)
  {
    case STDIN_FILENO:
      flags = O_RDONLY;
      name = "stdin";
      break;

    case STDOUT_FILENO:
    case STDERR_FILENO:
      flags = O_CREAT | O_WRONLY;
      mode = S_IRUSR | S_IWUSR;
      name = fd == STDOUT_FILENO ? "stdout" : "stderr";
      break;

    default: Assert(0);
  }

  const fdt result_fd = open(file.c_str(), flags, mode);

  if (result_fd == -1)
    perror(("Failed to open " + name + " file " + file).c_str());
  return result_fd;
}

int run(const std::string& what,
        const std::vector<std::string>& argv,
        const std::string& std_input,
        const std::string& std_output,
        const std::string& std_error)
{
  int stdin_fd = stdio_redirection(STDIN_FILENO, std_input);
  int stdout_fd = stdio_redirection(STDOUT_FILENO, std_output);
  int stderr_fd = stdio_redirection(STDERR_FILENO, std_error);

  if (stdin_fd == -1 || stdout_fd == -1 || stderr_fd == -1) return 1;

  // temporarily suspend all signals
  sigset_t new_mask, old_mask;
  sigemptyset(&new_mask);
  sigprocmask(SIG_SETMASK, &new_mask, &old_mask);

  /* now create new process */
  pid_t childpid = fork();

  if (childpid >= 0) /* fork succeeded */
  {
    if (childpid == 0) /* fork() returns 0 to the child process */
    {
      // resume signals
      remove_signal_catcher();
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      std::vector<char*> _argv(argv.size() + 1);
      for (size_t i = 0; i < argv.size(); i++)
        _argv[i] = strdup(argv[i].c_str());

      _argv[argv.size()] = nullptr;

      if (stdin_fd != STDIN_FILENO) dup2(stdin_fd, STDIN_FILENO);
      if (stdout_fd != STDOUT_FILENO) dup2(stdout_fd, STDOUT_FILENO);
      if (stderr_fd != STDERR_FILENO) dup2(stderr_fd, STDERR_FILENO);

      errno = 0;
      execvp(what.c_str(), _argv.data());

      /* usually no return */
      perror(std::string("execvp " + what + " failed").c_str());
      exit(1);
    }
    else /* fork() returns new pid to the parent process */
    {
      // must do before resuming signals to avoid race
      register_child(childpid);

      // resume signals
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      int status; /* parent process: child's exit status */

      /* wait for child to exit, and store its status */
      while (waitpid(childpid, &status, 0) == -1)
      {
        if (errno == EINTR)
          continue;  // try again
        else
        {
          unregister_child();

          perror("Waiting for child process failed");
          if (stdin_fd != STDIN_FILENO) close(stdin_fd);
          if (stdout_fd != STDOUT_FILENO) close(stdout_fd);
          if (stderr_fd != STDERR_FILENO) close(stderr_fd);
          return 1;
        }
      }

      unregister_child();

      if (stdin_fd != STDIN_FILENO) close(stdin_fd);
      if (stdout_fd != STDOUT_FILENO) close(stdout_fd);
      if (stderr_fd != STDERR_FILENO) close(stderr_fd);

      return WEXITSTATUS(status);
    }
  }
  else /* fork returns -1 on failure */
  {
    // resume signals
    sigprocmask(SIG_SETMASK, &old_mask, nullptr);

    if (stdin_fd != STDIN_FILENO) close(stdin_fd);
    if (stdout_fd != STDOUT_FILENO) close(stdout_fd);
    if (stderr_fd != STDERR_FILENO) close(stderr_fd);

    return 1;
  }
}

/// quote a  std::string for bash and CMD
std::string shell_quote(const std::string& src)
{
  // first check if quoting is needed at all

  if (src.find(' ') == std::string::npos && src.find('"') == std::string::npos
      && src.find('*') == std::string::npos
      && src.find('$') == std::string::npos
      && src.find('\\') == std::string::npos
      && src.find('?') == std::string::npos
      && src.find('&') == std::string::npos
      && src.find('|') == std::string::npos
      && src.find('>') == std::string::npos
      && src.find('<') == std::string::npos
      && src.find('^') == std::string::npos
      && src.find('#') == std::string::npos
      && src.find('\'') == std::string::npos)
  {
    // seems fine -- return as is
    return src;
  }

  std::string result;

  // the single quotes catch everything but themselves!
  result += '\'';

  for (const char ch : src)
  {
    if (ch == '\'')
    {
      // Special handling for single quote as we need to escape it
      // because of the surrounding single quotes.
      result += "'\\''";
      continue;
    }

    result += ch;
  }

  result += '\'';

  return result;
}

int run(const std::string& what,
        const std::vector<std::string>& argv,
        const std::string& std_input,
        std::ostream& std_output,
        const std::string& std_error)
{
  std::string command;

  bool first = true;

  // note we use 'what' instead of 'argv[0]' as the name of the executable
  for (const auto& arg : argv)
  {
    if (first)  // this is argv[0]
    {
      command += shell_quote(what);
      first = false;
    }
    else
      command += " " + shell_quote(arg);
  }

  if (!std_input.empty()) command += " < " + shell_quote(std_input);

  if (!std_error.empty()) command += " 2> " + shell_quote(std_error);
  
  FILE* stream = popen(command.c_str(), "r");

  if (stream != nullptr)
  {
    int ch;
    while ((ch = fgetc(stream)) != EOF)
    {
      std_output << (unsigned char)ch;
    }
    return pclose(stream);
  }
  else
    return -1;
}

}  // namespace cvc5
