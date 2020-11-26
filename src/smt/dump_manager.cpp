/*********************                                                        */
/*! \file dump_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the dump manager.
 **/

#include "smt/dump_manager.h"

#include "expr/expr_manager.h"
#include "options/smt_options.h"
#include "smt/dump.h"
#include "smt/node_command.h"

namespace CVC4 {
namespace smt {

DumpManager::DumpManager(OutputManager& om, context::UserContext* u)
    : d_outMgr(om),
      d_fullyInited(false),
      d_dumpCommands()
{
}

DumpManager::~DumpManager()
{
  d_dumpCommands.clear();
}

void DumpManager::finishInit()
{
  Trace("smt-debug") << "Dump declaration commands..." << std::endl;
  // dump out any pending declaration commands
  for (size_t i = 0, ncoms = d_dumpCommands.size(); i < ncoms; ++i)
  {
    Dump("declarations") << *d_dumpCommands[i];
  }
  d_dumpCommands.clear();

  d_fullyInited = true;
}
void DumpManager::resetAssertions()
{
  // currently, do nothing
}

void DumpManager::addToModelCommandAndDump(const NodeCommand& c,
                                           uint32_t flags,
                                           bool userVisible,
                                           const char* dumpTag)
{
  Trace("smt") << "SMT addToModelCommandAndDump(" << c << ")" << std::endl;
  if (Dump.isOn(dumpTag))
  {
    if (d_fullyInited)
    {
      Dump(dumpTag) << c;
    }
    else
    {
      d_dumpCommands.push_back(std::unique_ptr<NodeCommand>(c.clone()));
    }
  }
}

void DumpManager::setPrintFuncInModel(Node f, bool p)
{
  Trace("setp-model") << "Set printInModel " << f << " to " << p << std::endl;
  // TODO (cvc4-wishues/issues/75): implement
}


void DumpManager::nmNotifyNewSort(TypeNode tn, uint32_t flags)
{
  DeclareTypeNodeCommand c(tn.getAttribute(expr::VarNameAttr()), 0, tn);
  if ((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0)
  {
    d_dm.addToModelCommandAndDump(c, flags);
  }
}

void DumpManager::nmNotifyNewSortConstructor(TypeNode tn,
                                                        uint32_t flags)
{
  DeclareTypeNodeCommand c(tn.getAttribute(expr::VarNameAttr()),
                           tn.getAttribute(expr::SortArityAttr()),
                           tn);
  if ((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0)
  {
    d_dm.addToModelCommandAndDump(c);
  }
}

void DumpManager::nmNotifyNewDatatypes(
    const std::vector<TypeNode>& dtts, uint32_t flags)
{
  if ((flags & NodeManager::DATATYPE_FLAG_PLACEHOLDER) == 0)
  {
    if (Configuration::isAssertionBuild())
    {
      for (CVC4_UNUSED const TypeNode& dt : dtts)
      {
        Assert(dt.isDatatype());
      }
    }
    DeclareDatatypeNodeCommand c(dtts);
    d_dm.addToModelCommandAndDump(c);
  }
}

void DumpManager::nmNotifyNewVar(TNode n, uint32_t flags)
{
  DeclareFunctionNodeCommand c(
      n.getAttribute(expr::VarNameAttr()), n, n.getType());
  if ((flags & ExprManager::VAR_FLAG_DEFINED) == 0)
  {
    d_dm.addToModelCommandAndDump(c, flags);
  }
}

void DumpManager::nmNotifyNewSkolem(TNode n,
                                               const std::string& comment,
                                               uint32_t flags)
{
  std::string id = n.getAttribute(expr::VarNameAttr());
  DeclareFunctionNodeCommand c(id, n, n.getType());
  if (Dump.isOn("skolems") && comment != "")
  {
    d_outMgr.getPrinter().toStreamCmdComment(d_outMgr.getDumpOut(),
                                             id + " is " + comment);
  }
  if ((flags & ExprManager::VAR_FLAG_DEFINED) == 0)
  {
    d_dm.addToModelCommandAndDump(c, flags, false, "skolems");
  }
}

}  // namespace smt
}  // namespace CVC4
