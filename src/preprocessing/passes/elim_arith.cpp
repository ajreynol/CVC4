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

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_converter.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/theory.h"
#include "theory/uf/theory_uf_rewriter.h"

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
    Kind k = orig.getKind();
    Trace("elim-arith-convert") << "Convert term " << orig << " " << orig.getKind() << std::endl;
    TypeNode tn = orig.getType();
    if (orig.isVar())
    {
      TypeNode ctn = convertType(tn);
      if (ctn != tn)
      {
        Trace("elim-arith-convert") << "...type changed to " << ctn << " " << ctn.getKind() << " from " << tn << " " << tn.getKind() << std::endl;
        std::map<Node, Node>::iterator itd = d_dtSymCache.find(orig);
        if (itd != d_dtSymCache.end())
        {
          return itd->second;
        }
        if (k == Kind::BOUND_VARIABLE)
        {
          return d_nm->mkBoundVar(ctn);
        }
        else
        {
          // all constructor symbols should be caught by d_dtSymCache
          Assert(ctn.getKind() != Kind::CONSTRUCTOR_TYPE);
          Node vvar = d_nm->getSkolemManager()->mkDummySkolem("u_v", ctn);
          return vvar;
        }
      }
      return orig;
    }
    else if (orig.isConst() && tn.isRealOrInt())
    {
      TypeNode ctn = convertType(tn);
      Node cvar = d_nm->getSkolemManager()->mkDummySkolem("u_c",ctn);
      d_consts[tn].push_back(std::pair<Node,Node>(orig,cvar));
      return cvar;
    }
    else if (k != Kind::EQUAL
             && !Theory::isLeafOf(orig, THEORY_ARITH))
    {
      // make into chain
      if ((k==Kind::PLUS || k==Kind::MULT || k==Kind::NONLINEAR_MULT) && orig.getNumChildren()>2)
      {
        Node curr = orig[0];
        for (size_t i=1, nchild = orig.getNumChildren(); i<nchild; i++)
        {
          curr = nm->mkNode(k, orig[i]);
        }
        return convert(curr);
      }
      TypeNode ctn = convertType(tn);
      std::vector<TypeNode> argTypes;
      for (const Node& t : terms)
      {
        argTypes.push_back(t.getType());
      }
      TypeNode ftype = d_nm->mkFunctionType(argTypes, ctn);
      std::pair<TypeNode, Kind> key(ftype, k);
      std::map<std::pair<TypeNode, Kind>, Node>::iterator itc;
      itc = d_opCache.find(key);
      Node oop;
      if (itc!=d_opCache.end())
      {
        oop = itc->second;
      }
      else
      {
        oop = d_nm->getSkolemManager()->mkDummySkolem("u_op",ftype);
        d_opCache[key] = oop;
      }
      std::vector<Node> oterms;
      oterms.push_back(oop);
      oterms.insert(oterms.end(), terms.begin(), terms.end());
      return d_nm->mkNode(Kind::APPLY_UF, oterms);
    }
    else if (k == Kind::INST_PATTERN_LIST)
    {
      std::vector<Node> newChildren;
      for (const Node& t : terms)
      {
        if (t.getKind()!=Kind::INST_ATTRIBUTE)
        {
          newChildren.push_back(t);
        }
      }
      return d_nm->mkNode(k, newChildren);
    }
    else if (!terms.empty())
    {
      return d_nm->mkNode(k, terms);
    }
    return orig;
  }
  TypeNode postConvertType(TypeNode tn) override
  {
    Trace("elim-arith-convert") << "Convert type " << tn << " " << tn.getKind() << std::endl;
    if (tn.isRealOrInt())
    {
      std::map<TypeNode, TypeNode>::iterator it = d_arithCache.find(tn);
      if (it!=d_arithCache.end())
      {
        Trace("elim-arith-convert") << "...arith cached" << std::endl;
        return it->second;
      }
      std::stringstream ss;
      ss << "U" << tn;
      TypeNode ret = d_nm->mkSort(ss.str());
      d_arithCache[tn] = ret;
      Trace("elim-arith-convert") << "...arith" << std::endl;
      return ret;
    }
    if (tn.isDatatype())
    {
      std::map<TypeNode, TypeNode>::iterator it = d_dtCache.find(tn);
      if (it != d_dtCache.end())
      {
        Trace("elim-arith-convert") << "...already cached" << std::endl;
        return it->second;
      }
      Trace("elim-arith-convert") << "Convert datatype " << tn << std::endl;
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
        Trace("elim-arith-convert") << "...process " << curr << " " << curr.getKind() << std::endl;
        if (connected.find(curr) != connected.end())
        {
          continue;
        }
        connected.insert(curr);
        if (curr.isDatatype())
        {
          it = d_dtCache.find(curr);
          if (it != d_dtCache.end())
          {
            // a previously converted datatype
            needsUpdate = needsUpdate || it->second != curr;
            converted[curr] = it->second;
            Trace("elim-arith-convert") << "......already cache dt" << std::endl;
          }
          else
          {
            connectedDt.push_back(curr);
            const DType& dt = tn.getDType();
            std::unordered_set<TypeNode> stypes = dt.getSubfieldTypes();
            toProcess.insert(toProcess.end(), stypes.begin(), stypes.end());
            Trace("elim-arith-convert") << "......new dt, subfield types is " << stypes.size() << std::endl;
          }
        }
        else
        {
          TypeNode ccurr = convertType(curr);
          needsUpdate = needsUpdate || ccurr != curr;
          converted[curr] = ccurr;
          Trace("elim-arith-convert") << "......non dt" << std::endl;
        }
      } while (!toProcess.empty());
      Trace("elim-arith-convert")
          << "...needs update is " << needsUpdate << std::endl;
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
          ss << "u_" << curr.getDType().getName();
          newDatatypes.push_back(DType(ss.str()));
          converted[curr] = d_nm->mkUnresolvedDatatypeSort(ss.str());
        }
        for (size_t d = 0, numDts = connectedDt.size(); d < numDts; d++)
        {
          TypeNode curr = connectedDt[d];
          DType& ndt = newDatatypes[d];
          const DType& dt = curr.getDType();
          for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
          {
            const DTypeConstructor& dc = dt[i];
            std::stringstream ssc;
            ssc << "u_" << dc.getName();
            std::shared_ptr<DTypeConstructor> c =
                std::make_shared<DTypeConstructor>(ssc.str());
            for (size_t j = 0, nargs = dc.getNumArgs(); j < nargs; j++)
            {
              std::stringstream sss;
              sss << "u_" << dc[j].getName();
              c->addArg(sss.str(), converted[dc[j].getRangeType()]);
            }
            ndt.addConstructor(c);
          }
        }
        std::vector<TypeNode> ndts = d_nm->mkMutualDatatypeTypes(newDatatypes);
        Assert(ndts.size() == connectedDt.size());
        for (size_t d = 0, numDts = connectedDt.size(); d < numDts; d++)
        {
          d_dtCache[connectedDt[d]] = ndts[d];
          const DType& ndt = ndts[d].getDType();
          const DType& odt = connectedDt[d].getDType();
          for (size_t i = 0, ncons = ndt.getNumConstructors(); i < ncons; i++)
          {
            const DTypeConstructor& ndc = ndt[i];
            const DTypeConstructor& odc = odt[i];
            for (size_t j = 0, nargs = ndc.getNumArgs(); j < nargs; j++)
            {
              d_dtSymCache[odc[j].getSelector()] = ndc[j].getSelector();
              d_dtSymCache[odc[j].getUpdater()] = ndc[j].getUpdater();
            }
            d_dtSymCache[odc.getConstructor()] = ndc.getConstructor();
            d_dtSymCache[odc.getTester()] = ndc.getTester();
          }
        }
      }
      return d_dtCache[tn];
    }
    else
    {
      Trace("elim-arith-convert") << "...non-datatype" << std::endl;
    }
    return tn;
  }
  //----------------------
  std::map<TypeNode, std::vector<std::pair<Node, Node>>> d_consts;
  std::map<TypeNode, TypeNode> d_arithCache;
  std::map<TypeNode, TypeNode> d_dtCache;
  std::map<Node, Node> d_dtSymCache;
  std::map<std::pair<TypeNode, Kind>, Node> d_opCache;
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
    a = rewrite(a);
    Node ac = eac.convert(a, false);
    Trace("elim-arith") << "Converted " << a << " to " << ac << std::endl;
    assertionsToPreprocess->replace(i, rewrite(ac));
  }
  // all constants are distinct
  for (const std::pair<const TypeNode, std::vector<std::pair<Node, Node>>>& c : eac.d_consts)
  {
    if (c.second.size()<=1)
    {
      continue;
    }
    std::vector<Node> uconsts;
    for (const std::pair<Node, Node>& cs : c.second)
    {
      uconsts.push_back(cs.second);
    }
    Node distinct = nodeManager()->mkNode(Kind::DISTINCT, uconsts);
    assertionsToPreprocess->push_back(distinct);
  }
  for (const std::pair&<const std::pair<TypeNode, Kind>, Node>& op : d_opCache)
  {
    Kind k = op.first.second;
    if (k==Kind::GEQ)
    {
      
    }
    else if (k==Kind::PLUS)
    {
      
    }
  }
  
  // add additional assertions
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
