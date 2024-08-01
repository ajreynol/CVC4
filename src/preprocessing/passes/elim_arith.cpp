/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ElimArith preprocessing pass.
 *
 * Converts real operations into integer operations.
 */

#include "preprocessing/passes/elim_arith.h"

#include <string>

#include "expr/node_converter.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/theory.h"
#include "theory/uf/opaque_value.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class ElimArithConverter : public NodeConverter
{
 public:
  ElimArithConverter(NodeManager* nm) : NodeConverter(nm) {}

  Node postConvertUntyped(Node orig,
                          const std::vector<Node>& terms,
                          bool termsChanged) override
  {
    Trace("elim-arith-convert") << "Convert " << orig << std::endl;
    TypeNode tn = orig.getType();
    if (orig.isVar())
    {
      TypeNode ctn = convertType(tn);
      if (ctn != tn)
      {
        std::map<Node, Node>::iterator itd = d_dtSymCache.find(orig);
        if (itd != d_dtSymCache.end())
        {
          return itd->second;
        }
        if (orig.getKind() == Kind::BOUND_VARIABLE)
        {
          return d_nm->mkBoundVar(ctn);
        }
        else
        {
          SkolemManager* sm = d_nm->getSkolemManager();
          return sm->mkInternalSkolemFunction(
              InternalSkolemId::PURIFY_OPAQUE, ctn, {orig});
        }
      }
      return orig;
    }
    else if (orig.isConst() && tn.isRealOrInt())
    {
      return d_nm->mkConst(OpaqueValue(orig));
    }
    else if (orig.getKind()!=Kind::EQUAL && !Theory::isLeafOf(orig, THEORY_ARITH))
    {
      TypeNode ctn = convertType(tn);
      std::vector<TypeNode> argTypes;
      for (const Node& t : terms)
      {
        argTypes.push_back(t.getType());
      }
      TypeNode ftype = d_nm->mkFunctionType(argTypes, ctn);
      Node oop = theory::uf::TheoryUfRewriter::getOpaqueOperator(orig, ftype);
      std::vector<Node> oterms;
      oterms.push_back(oop);
      oterms.insert(oterms.end(), terms.begin(), terms.end());
      return d_nm->mkNode(Kind::APPLY_OPAQUE, oterms);
    }
    else if (!terms.empty())
    {
      Kind k = orig.getKind();
      return d_nm->mkNode(k, terms);
    }
    return orig;
  }
  TypeNode postConvertType(TypeNode tn) override
  {
    if (tn.isRealOrInt())
    {
      return d_nm->mkOpaqueType(tn);
    }
    if (tn.isDatatype())
    {
      std::map<TypeNode, TypeNode>::iterator it = d_dtCache.find(tn);
      if (it !=d_dtCache.end())
      {
        return it->second;
      }
      std::vector<TypeNode> toProcess;
      std::unordered_set<TypeNode> connected;
      std::vector<TypeNode> connectedDt;
      std::map<TypeNode, TypeNode> converted;
      bool needsUpdate = false;
      toProcess.push_back(tn);
      do
      {
        TypeNode curr = toProcess.back();
        toProcess.pop_back();
        if (connected.find(curr)!=connected.end())
        {
          continue;
        }
        connected.insert(curr);
        if (curr.isDatatype())
        {
          connectedDt.push_back(curr);
          const DType& dt = tn.getDType();
          std::unordered_set<TypeNode> stypes = dt.getSubfieldTypes();
          toProcess.insert(toProcess.end(), stypes.begin(), stypes.end());
        }
        else
        {
          TypeNode ccurr = convertType(curr);
          needsUpdate = needsUpdate || ccurr!=curr;
          converted[curr] = ccurr;
        }
      }while(!toProcess.empty());
      if (!needsUpdate)
      {
        for (const TypeNode& curr : connected)
        {
          d_dtCache[curr] = curr;
        }
      }
      else
      {
        std::vector<DType> newDatatypes;
        for (const TypeNode& curr : connectedDt)
        {
          std::stringstream ss;
          ss << "opaque_" << curr.getDType().getName();
          newDatatypes.push_back(DType(ss.str()));
          converted[curr] = d_nm->mkUnresolvedDatatypeSort(ss.str());
        }
        for (size_t d=0, numDts = connectedDt.size(); d<numDts; d++)
        {
          TypeNode curr = connectedDt[d];
          DType& ndt = newDatatypes[d];
          const DType& dt = curr.getDType();
          for (size_t i=0, ncons = dt.getNumConstructors(); i<ncons; i++)
          {
            const DTypeConstructor& dc = dt[i];
            std::stringstream ssc;
            ssc << "opaque_" << dc.getName();
            std::shared_ptr<DTypeConstructor> c =
                std::make_shared<DTypeConstructor>(ssc.str());
            for (size_t j=0, nargs = dc.getNumArgs(); j<nargs; j++)
            {
              std::stringstream sss;
              sss << "opaque_" << dc[j].getName();
              c->addArg(sss.str(), converted[dc[j].getRangeType()]);
            }
            ndt.addConstructor(c);
          }
        }
        std::vector<TypeNode> ndts = d_nm->mkMutualDatatypeTypes(newDatatypes);
        Assert (ndts.size()==connectedDt.size());
        for (size_t d=0, numDts = connectedDt.size(); d<numDts; d++)
        {
          d_dtCache[connectedDt[d]] = ndts[d];
          const DType& ndt = ndts[d].getDType();
          const DType& odt = connectedDt[d].getDType();
          for (size_t i=0, ncons = ndt.getNumConstructors(); i<ncons; i++)
          {
            const DTypeConstructor& ndc = ndt[i];
            const DTypeConstructor& odc = odt[i];
            for (size_t j=0, nargs = ndc.getNumArgs(); j<nargs; j++)
            {
              d_dtSymCache[odc[j].getSelector()] = ndc[j].getSelector();     
              d_dtSymCache[odc[j].getUpdater()] = ndc[j].getUpdater();             
            }
            d_dtSymCache[odc.getConstructor()] = ndc.getConstructor();
            d_dtSymCache[odc.getTester()] = ndc.getTester();
          }
        }
      }
    }
    return tn;
  }
private:
  std::map<TypeNode, TypeNode> d_dtCache;
  std::map<Node, Node> d_dtSymCache;
};

ElimArith::ElimArith(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "elim-arith")
{
}

PreprocessingPassResult ElimArith::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  ElimArithConverter eac(nodeManager());
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    Node ac = eac.convert(a, false);
    Trace("elim-arith") << "Converted " << a << " to " << ac << std::endl;
    assertionsToPreprocess->replace(i, rewrite(ac));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
