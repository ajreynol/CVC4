#include "theory/quantifiers/contextual_enumerator.h"

#include "expr/skolem_manager.h"
#include "expr/sygus_grammar.h"
#include "expr/sygus_term_enumerator.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ContextualEnumerator::ContextualEnumerator(Env& env,
                                           QuantifiersState& qs,
                                           QuantifiersInferenceManager& qim,
                                           QuantifiersRegistry& qr,
                                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

ContextualEnumerator::~ContextualEnumerator() {}

bool ContextualEnumerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void ContextualEnumerator::reset_round(Theory::Effort e) {}

void ContextualEnumerator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    // We want to enumerate terms for the operators op_0, ..., op_n and
    // enum_queue is op_0(...), ..., op_n(...).
    std::vector<Node> enum_queue = collectSignatureInformation();

    if (TraceIsOn("ctx-enum-queue"))
    {
      debugPrintEnumQueue(enum_queue);
    }

    enumerateUf(enum_queue);
  }
}

std::string ContextualEnumerator::identify() const
{
  return "contextual-enumerator";
}

std::vector<Node> ContextualEnumerator::collectSignatureInformation()
{
  TermDb* const term_db = getTermDatabase();

  std::vector<Node> enum_queue;

  // The number of function symbols in the current signature.
  const size_t num_ops = term_db->getNumOperators();

  for (size_t i = 0; i < num_ops; i++)
  {
    // The i th function symbol in the current signature.
    const Node& op = term_db->getOperator(i);

    // The list of ground terms with 'op' as the root function symbol.
    DbList* const db_list = term_db->getOrMkDbListForOp(op);

    if (!db_list->d_list.empty())
    {
      // An arbitrary ground term with root function symbol 'op'.
      const Node& op_term = db_list->d_list[0];

      if (isHandledTerm(op_term) && op_term.getKind() != Kind::APPLY_SELECTOR
          && !op_term.getType().isBoolean())
      {
        if (d_uf_enum.find(op) == d_uf_enum.end())
        {
          if (TraceIsOn("ctx-enum-queue"))
          {
            Trace("ctx-enum-queue") << "Tried to find " << op << " in "
                                    << " d_uf_enum but failed." << std::endl;
            Trace("ctx-enum-queue") << "d_uf_enum is {";
            for (std::unordered_set<Node>::iterator j = d_uf_enum.begin();
                 j != d_uf_enum.end();
                 j++)
            {
              Trace("ctx-enum-queue") << " " << *j;
            }
            Trace("ctx-enum-queue") << " }" << std::endl;
          }

          enum_queue.push_back(op_term);
        }
      }
    }
  }

  return enum_queue;
}

void ContextualEnumerator::enumerateUf(const std::vector<Node>& enum_queue)
{
  for (const Node& queued_term : enum_queue)
  {
    if (d_uf_enum.find(queued_term) == d_uf_enum.end())
    {
      const Node& op = queued_term.getOperator();

      d_uf_enum.insert(op);

      // We will submit one enumeration lemma for each element in the vector
      // enum_terms.

      const Node& pred = getPredicateForType(queued_term.getType());

      const std::vector<Node>& gend_terms =
          enumerateTermsWithSygus(queued_term);

      if (TraceIsOn("ctx-enum-generated"))
      {
        Trace("ctx-enum-generated")
            << "Terms generated for " << op << ":" << std::endl;

        for (const Node& term : gend_terms)
        {
          Trace("ctx-enum-generated") << "* " << term << std::endl;
        }
      }

      for (const Node& term : gend_terms)
      {
        const Node& lem = nodeManager()->mkNode(Kind::APPLY_UF, pred, term);

        d_qim.addPendingLemma(lem, InferenceId::QUANTIFIERS_CTX_ENUM);
      }

      d_hasAddedLemma = true;
    }
  }
}

bool ContextualEnumerator::isHandledTerm(const TNode n)
{
  return getTermDatabase()->isTermActive(n)
         && inst::TriggerTermInfo::isAtomicTrigger(n)
         && (n.getKind() != Kind::APPLY_UF
             || n.getOperator().getKind() != Kind::SKOLEM);
}

Node ContextualEnumerator::getPredicateForType(TypeNode typ)
{
  auto it = d_typ_pred.find(typ);

  if (it != d_typ_pred.end())
  {
    return it->second;
  }
  else
  {
    NodeManager* node_mgr = nodeManager();

    TypeNode pred_typ = node_mgr->mkFunctionType(typ, node_mgr->booleanType());

    Node pred = NodeManager::mkDummySkolem(
        "PE",
        pred_typ,
        "was created by the contextual ground term enumerator.");

    d_typ_pred[typ] = pred;

    return pred;
  }
}

std::vector<Node> ContextualEnumerator::enumerateTermsWithSygus(TNode root_term)
{
  // Suppose we have a function symbol 'f' with argument types 'T', 'U' and
  // result type 'V'.  We intend to construct a grammar that enumerates
  // f-applications.  The grammar's root non-terminal should be:
  //
  //     N_V ::= f(N_T, N_U)
  //
  // Here 'N_V', 'N_T', and 'N_U' are a non-terminals of type V, T, and U
  // respectively.  We'll use methods from the SygusGrammarCons class to create
  // grammars for T and U.  Cache the grammar for each argument type.  Don't
  // worry about any further sharing since it's probably an excessive
  // optimization.

  // Prepare the map from argument types to their grammars.

  std::map<TypeNode, SygusGrammar> arg_typ_to_gr;

  for (auto arg : root_term)
  {
    TypeNode typ = arg.getType();

    if (arg_typ_to_gr.find(typ) == arg_typ_to_gr.end())
    {
      arg_typ_to_gr.emplace(std::make_pair(
          typ, SygusGrammarCons::mkDefaultGrammar(d_env, typ, Node::null())));
    }
  }

  // We'll transform all argument grammars in the following manner.
  //
  // 1.  For all datatype-sorted non-terminals remove any rule with kind ITE or
  // APPLY_SELECTOR.
  //
  // 2.  For all other non-terminals remove all rules and replace with the 'any
  // constant' rule.

  for (std::map<TypeNode, SygusGrammar>::iterator typ_gr_pair =
           arg_typ_to_gr.begin();
       typ_gr_pair != arg_typ_to_gr.end();
       typ_gr_pair++)
  {
    SygusGrammar& gr = typ_gr_pair->second;

    // Collect all the rules that we need to remove from the grammar.

    std::vector<std::pair<Node, Node>> rules_to_remove;

    for (const Node& nt : gr.getNtSyms())
    {
      for (const Node& rule : gr.getRulesFor(nt))
      {
        if (nt.getType().isDatatype())
        {
          if (rule.getKind() == Kind::ITE
              || rule.getKind() == Kind::APPLY_SELECTOR)
          {
            rules_to_remove.emplace_back(std::pair<Node, Node>{nt, rule});
          }
        }
        else
        {
          rules_to_remove.emplace_back(std::pair<Node, Node>{nt, rule});
        }
      }
    }

    // Remove all the rules as intended.

    for (std::vector<std::pair<Node, Node>>::iterator nt_rule_pair =
             rules_to_remove.begin();
         nt_rule_pair != rules_to_remove.end();
         nt_rule_pair++)
    {
      gr.removeRule(nt_rule_pair->first, nt_rule_pair->second);
    }

    // Add 'any constant' rules for non-terminals that have types that are not
    // inductive datatypes.

    for (const Node& nt : gr.getNtSyms())
    {
      const TypeNode& typ = nt.getType();

      if (!typ.isDatatype())
      {
        gr.addAnyConstant(nt, typ);
      }
    }
  }

  // Isolate the root non-terminal for each argument's grammar.  For example, I
  // expect type T's grammar to have exactly one non-terminal of type T.  This
  // non-terminal is treated as the start non-terminal.

  std::map<TypeNode, Node> arg_typ_to_nt;

  for (auto entry : arg_typ_to_gr)
  {
    TypeNode arg_typ = entry.first;

    for (auto nt : entry.second.getNtSyms())
    {
      if (nt.getType() == arg_typ)
      {
        arg_typ_to_nt[arg_typ] = nt;

        break;
      }
    }
  }

  // Manufacture the "root" non-terminal -- the one responsible for producing
  // all f-applications.

  Node root_nt = nodeManager()->getSkolemManager()->mkDummySkolem(
      "root_nt", root_term.getType());

  // Collect all the non-terminals -- all non-terminals across all argument
  // grammars as well as the non-terminal for the f-applications.  (Lead with
  // the non-terminal for f-applications!)

  std::vector<Node> all_nts{root_nt};

  for (auto entry : arg_typ_to_gr)
  {
    std::vector<Node> arg_gr_nts = entry.second.getNtSyms();
    all_nts.insert(all_nts.end(), arg_gr_nts.begin(), arg_gr_nts.end());
  }

  // Use the master list of non-terminals to construct the root grammar.

  SygusGrammar root_gr(std::vector<Node>{}, all_nts);

  // Make the sole production rule for the root non-terminal.

  std::vector<Node> root_rule_args{root_term.getOperator()};

  for (auto arg : root_term)
  {
    root_rule_args.push_back(arg_typ_to_nt[arg.getType()]);
  }

  Node root_rule = nodeManager()->mkNode(root_term.getKind(), root_rule_args);

  // Associate root_rule with root_nt in root_gr.

  root_gr.addRule(root_nt, root_rule);

  // Add all rules for all non-terminals across all argument grammars to the
  // root grammar.

  for (auto entry : arg_typ_to_gr)
  {
    SygusGrammar gr = entry.second;

    for (auto nt : gr.getNtSyms())
    {
      for (auto rule : gr.getRulesFor(nt))
      {
        root_gr.addRule(nt, rule);
      }
    }
  }

  // Before we resolve the grammar let's make sure we have exactly what we need
  // by printing all its non-terminals and associated rules.

  if (TraceIsOn("ctx-enum-grammar"))
  {
    Trace("ctx-enum-grammar")
        << "Here are rules for each non-terminal." << std::endl;
    for (auto nt : root_gr.getNtSyms())
    {
      Trace("ctx-enum-grammar") << "* " << nt << ":" << std::endl;
      for (auto rule : root_gr.getRulesFor(nt))
      {
        Trace("ctx-enum-grammar") << "  * " << rule << std::endl;
      }
    }
  }

  // We need to resolve the grammar, quitting early if resolution fails.

  const TypeNode& root_gr_typ = root_gr.resolve();

  Assert(root_gr.isResolved());

  // Declare the vector that we'll use to store the terms we generate.  Let's
  // also pre-emptively grab the maxium number of terms we will generate for
  // each function symbol.

  std::vector<Node> gend_terms;

  const int64_t limit = options().quantifiers.contextualEnumeratorLimit;

  // Make an enumeration type to store our preference among the
  // SygusTermEnumerator and the SygusSampler.

  switch (options().quantifiers.contextualEnumeratorStrategy)
  {
    case options::ContextualEnumeratorStrategy::ENUMERATE:
    {
      SygusTermEnumerator root_gr_enum(d_env, root_gr_typ);

      // Let's keep going till either increment() returns false or we generate
      // contextualEnumeratorLimit-many terms.

      int64_t n_gend_terms = 0;

      // **Note**.  first_time should be false when n_gend_terms >= limit and
      // true otherwise.

      bool first_time = n_gend_terms < limit;

      while (first_time || (n_gend_terms < limit && root_gr_enum.increment()))
      {
        if (first_time)
        {
          first_time = false;
        }

        const Node& curr_term = root_gr_enum.getCurrent();

        if (!curr_term.isNull())
        {
          gend_terms.push_back(curr_term);

          n_gend_terms++;
        }
      }

      break;
    }

    case options::ContextualEnumeratorStrategy::SAMPLE:
    {
      // To start with we construct and initialize the sampler.

      SygusSampler root_gr_sampler = SygusSampler(d_env);

      const Node& root_gr_var =
          nodeManager()->getSkolemManager()->mkDummySkolem("sampler_",
                                                           root_gr_typ);

      root_gr_sampler.initialize(
          root_gr_typ, std::vector<Node>{root_gr_var}, limit);

      // We *requested* limit-many points but actually generated
      // n_sample_pts-many points.

      const size_t n_sample_pts = root_gr_sampler.getNumSamplePoints();

      Trace("ctx-enum-sampler")
          << "Actually generated " << n_sample_pts << " points." << std::endl;

      for (size_t i = 0; i < n_sample_pts; i++)
      {
        const std::vector<Node>& sample_pt = root_gr_sampler.getSamplePoint(i);

        // We've requested only one term because the vector we passed to
        // initialize has length exactly 1.  We'll error out if we have any more
        // or any less terms.

        Assert(sample_pt.size() == 1);

        // At this point we're sure that sample_pt contains exactly one term.
        // This is a SyGuS term.  However we want the term it represents,
        // otherwise known as a builtin term.

        gend_terms.push_back(d_treg.getTermDatabaseSygus()->sygusToBuiltin(
            sample_pt.back(), root_gr_typ));
      }

      break;
    }
  }

  // Let's return the terms that we have generated using the grammar.

  return gend_terms;
}

void ContextualEnumerator::debugPrintEnumQueue(
    const std::vector<Node>& enum_queue)
{
  Trace("ctx-enum-queue") << "enum_queue = [";
  bool first_time = true;
  for (auto term : enum_queue)
  {
    if (first_time)
    {
      first_time = false;
    }
    else
    {
      Trace("ctx-enum-queue") << ", ";
    }
    Trace("ctx-enum-queue") << term.getOperator();
  }
  Trace("ctx-enum-queue") << "]" << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
