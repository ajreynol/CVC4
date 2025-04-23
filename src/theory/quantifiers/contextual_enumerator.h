#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CONTEXTUAL_ENUMERATOR_H
#define CVC5__THEORY__QUANTIFIERS__CONTEXTUAL_ENUMERATOR_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class ContextualEnumerator : public QuantifiersModule
{
 private:
  bool d_hasAddedLemma;
  std::unordered_set<Node> d_uf_enum;
  std::map<TypeNode, Node> d_typ_pred;

  std::vector<Node> collectSignatureInformation();
  void enumerateUf(const std::vector<Node>& enum_queue);
  std::vector<Node> enumerateTermsWithSygus(TNode term);
  bool isHandledTerm(const TNode n);
  Node getPredicateForType(TypeNode tn);
  void debugPrintEnumQueue(const std::vector<Node>& enum_queue);

 public:
  ContextualEnumerator(Env& env,
                       QuantifiersState& qs,
                       QuantifiersInferenceManager& qim,
                       QuantifiersRegistry& qr,
                       TermRegistry& tr);
  ~ContextualEnumerator();
  bool needsCheck(Theory::Effort e) override;
  void reset_round(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  std::string identify() const override;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__CONTEXTUAL_ENUMERATOR_H */
