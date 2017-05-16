/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **
 **/
#include "theory/quantifiers/ce_guided_instantiation.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_engine.h"
#include "prop/prop_engine.h"
#include "theory/bv/theory_bv_rewriter.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {


CegConjecture::CegConjecture( QuantifiersEngine * qe, context::Context* c )
    : d_qe( qe ), d_curr_lit( c, 0 ) {
  d_refine_count = 0;
  d_ceg_si = new CegConjectureSingleInv( qe, this );
  d_ceg_pbe = new CegConjecturePbe( qe, this );
}

CegConjecture::~CegConjecture() {
  delete d_ceg_si;
  delete d_ceg_pbe;
}

void CegConjecture::assign( Node q ) {
  Assert( d_quant.isNull() );
  Assert( q.getKind()==FORALL );
  d_assert_quant = q;
  //register with single invocation if applicable
  if( d_qe->getTermDatabase()->isQAttrSygus( d_assert_quant ) && options::cegqiSingleInvMode()!=CEGQI_SI_MODE_NONE ){
    d_ceg_si->initialize( q );
    if( q!=d_ceg_si->d_quant ){
      //Node red_lem = NodeManager::currentNM()->mkNode( OR, q.negate(), d_cegqi_si->d_quant );
      //may have rewritten quantified formula (for invariant synthesis)
      q = d_ceg_si->d_quant;
    }
  }
  if( options::sygusPbe() ){
    // check if it is only applied to concrete examples
    d_ceg_pbe->initialize( q );
  }
  d_quant = q;
  Assert( d_candidates.empty() );
  std::vector< Node > vars;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    vars.push_back( q[0][i] );
    Node e = NodeManager::currentNM()->mkSkolem( "e", q[0][i].getType() );
    d_candidates.push_back( e );
    // register this term with sygus database
    d_qe->getTermDatabaseSygus()->registerMeasuredTerm( e, e );
    if( options::sygusPbe() ){
      std::vector< std::vector< Node > > exs;
      std::vector< Node > exos;
      std::vector< Node > exts;
      if( d_ceg_pbe->getPbeExamples( q[0][i], e, exs, exos, exts ) ){
        d_qe->getTermDatabaseSygus()->registerPbeExamples( e, exs, exos, exts );
      }
    }
  }
  Trace("cegqi") << "Base quantified formula is : " << q << std::endl;
  //construct base instantiation
  d_base_inst = Rewriter::rewrite( d_qe->getInstantiation( q, vars, d_candidates ) );
  Trace("cegqi") << "Base instantiation is :      " << d_base_inst << std::endl;
  if( d_qe->getTermDatabase()->isQAttrSygus( d_assert_quant ) ){
    CegInstantiation::collectDisjuncts( d_base_inst, d_base_disj );
    Trace("cegqi") << "Conjecture has " << d_base_disj.size() << " disjuncts." << std::endl;
    //store the inner variables for each disjunct
    for( unsigned j=0; j<d_base_disj.size(); j++ ){
      Trace("cegqi") << "  " << j << " : " << d_base_disj[j] << std::endl;
      d_inner_vars_disj.push_back( std::vector< Node >() );
      //if the disjunct is an existential, store it
      if( d_base_disj[j].getKind()==NOT && d_base_disj[j][0].getKind()==FORALL ){
        for( unsigned k=0; k<d_base_disj[j][0][0].getNumChildren(); k++ ){
          d_inner_vars.push_back( d_base_disj[j][0][0][k] );
          d_inner_vars_disj[j].push_back( d_base_disj[j][0][0][k] );
        }
      }
    }

    if( options::sygusUnifCondSolNew() ){
      if( d_candidates.size()==1 ){  // conditional solutions for multiple function conjectures TODO?
        std::vector< TypeNode > tne;
        std::map< TypeNode, bool > visited;
        // collect a pool of types over which we will enumerate terms 
        Node e = d_candidates[0];
        collectEnumeratorTypes( e, e.getType() );
        // now construct the enumerators
        for( std::map< TypeNode, EnumTypeInfo >::iterator iti = d_einfo.begin(); iti != d_einfo.end(); ++iti ){
          TypeNode tn = iti->first;
          // register type
          Node ee = NodeManager::currentNM()->mkSkolem( "ee", tn );
          d_esyms[tn][-1] = ee;
          registerEnumerator( ee, e, tn, -1 );
          Trace("sygus-unif-debug") << "...enumerate " << ee << " for " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
          for( unsigned j=0; j<iti->second.d_csol_cts.size(); j++ ){
            if( iti->second.d_template.find( j )!=iti->second.d_template.end() ){
              // it is templated, allocate a fresh variable
              Node et = NodeManager::currentNM()->mkSkolem( "et", iti->second.d_csol_cts[j] );
              Trace("sygus-unif-debug") << "...enumerate " << et << " of type " << ((DatatypeType)iti->second.d_csol_cts[j].toType()).getDatatype().getName();
              Trace("sygus-unif-debug") << " for arg " << j << " of " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
              registerEnumerator( et, e, tn, j );
            }
          }
        }
      }
    }
    d_syntax_guided = true;
  }else if( d_qe->getTermDatabase()->isQAttrSynthesis( d_assert_quant ) ){
    d_syntax_guided = false;
  }else{
    Assert( false );
  }
}

void CegConjecture::registerEnumerator( Node et, Node e, TypeNode tn, int j ) {
  d_qe->getTermDatabaseSygus()->registerMeasuredTerm( et, e );
  d_esyms[tn][j] = et;
  d_esym_to_parent[et] = tn;
  if( j>=0 ){
    d_esym_to_arg[et] = j;
  }
  // make the guard
}

void CegConjecture::collectEnumeratorTypes( Node e, TypeNode tn ) {
  if( d_einfo.find( tn )==d_einfo.end() ){
    d_einfo[tn].d_csol_status = 0;
    Trace("sygus-unif") << "Register enumerating type : " << tn << std::endl;
    Assert( tn.isDatatype() );
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    Assert( dt.isSygus() );
    bool success = false;
    for( unsigned r=0; r<2; r++ ){
      for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
        Node op = Node::fromExpr( dt[j].getSygusOp() );
        if( r==0 ){
          if( op.getKind() == kind::BUILTIN ){
            Kind sk = NodeManager::operatorToKind( op );
            if( sk==kind::ITE ){
              Trace("sygus-unif") << "...type " << dt.getName() << " has ITE, enumerate child types..." << std::endl;
              // we can do unification
              success = true;
              d_einfo[tn].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
              Assert( dt[j].getNumArgs()==3 );
              for( unsigned k=0; k<3; k++ ){
                TypeNode ct = TypeNode::fromType( dt[j][k].getRangeType() );
                Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)ct.toType()).getDatatype().getName() << std::endl;
                d_einfo[tn].d_csol_cts.push_back( ct );
                collectEnumeratorTypes( e, ct );
              }
              break;
            }
          }
        }else{
          if( dt[j].getNumArgs()>=3 ){
            // could be a defined ITE (this is a hack for ICFP benchmarks)
            std::vector< Node > utchildren;
            utchildren.push_back( Node::fromExpr( dt[j].getConstructor() ) );
            std::vector< Node > sks;
            std::vector< TypeNode > sktns;
            for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
              Type t = dt[j][k].getRangeType();
              TypeNode ttn = TypeNode::fromType( t );
              Node kv = NodeManager::currentNM()->mkSkolem( "ut", ttn );
              sks.push_back( kv );
              sktns.push_back( ttn );
              utchildren.push_back( kv );
            }
            Node ut = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, utchildren );
            std::vector< Node > echildren;
            echildren.push_back( Node::fromExpr( dt.getSygusEvaluationFunc() ) );
            echildren.push_back( ut );
            Node sbvl = Node::fromExpr( dt.getSygusVarList() );
            for( unsigned k=0; k<sbvl.getNumChildren(); k++ ){
              echildren.push_back( sbvl[k] );
            }
            Node eut = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
            Trace("sygus-unif-debug") << "Test evaluation of " << eut << "..." << std::endl;
            eut = d_qe->getTermDatabaseSygus()->unfold( eut );
            Trace("sygus-unif-debug") << "...got " << eut << std::endl;
            if( eut.getKind()==kind::ITE ){
              success = true;
              std::vector< Node > vs;
              std::vector< Node > ss;
              std::map< Node, unsigned > templ_var_index;
              for( unsigned k=0; k<sks.size(); k++ ){
                echildren[1] = sks[k];
                Node esk = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
                vs.push_back( esk );
                Node tvar = NodeManager::currentNM()->mkSkolem( "templ", esk.getType() );
                templ_var_index[tvar] = k;
                ss.push_back( tvar );
              }
              eut = eut.substitute( vs.begin(), vs.end(), ss.begin(), ss.end() );
              Trace("sygus-unif-debug") << "Defined constructor " << j << ", base term is " << eut << std::endl;
              //success if we can find a injection from ITE args to sygus args
              std::map< unsigned, unsigned > templ_injection;
              for( unsigned k=0; k<3; k++ ){
                if( !inferIteTemplate( k, eut[k], templ_var_index, templ_injection ) ){
                  Trace("sygus-unif-debug") << "...failed to find injection (range)." << std::endl;
                  success = false;
                  break;
                }
                if( templ_injection.find( k )==templ_injection.end() ){
                  Trace("sygus-unif-debug") << "...failed to find injection (domain)." << std::endl;
                  success = false;
                  break;
                }
              }
              if( success ){
                Trace("sygus-unif") << "...type " << dt.getName() << "has ITE-like constructor, enumerate child types..." << std::endl;
                d_einfo[tn].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
                for( unsigned k=0; k<3; k++ ){
                  Assert( templ_injection.find( k )!=templ_injection.end() );
                  unsigned sk_index = templ_injection[k];
                  //also store the template information, if necessary
                  Node teut = eut[k];
                  if( !teut.isVar() ){
                    d_einfo[tn].d_template[k] = teut;
                    d_einfo[tn].d_template_arg[k] = ss[sk_index];
                    Trace("sygus-unif") << "  Arg " << k << " : template : " << teut << ", arg " << ss[sk_index] << std::endl;
                  }else{
                    Assert( teut==ss[sk_index] );
                  }
                }
                // collect children types
                for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                  Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)sktns[k].toType()).getDatatype().getName() << std::endl;
                  d_einfo[tn].d_csol_cts.push_back( sktns[k] );
                  collectEnumeratorTypes( e, sktns[k] );
                }
              }
            }
          }
        }
      }
      if( success ){
        break;
      }
    }
    if( !success ){
      Trace("sygus-unif") << "...consider " << dt.getName() << " a basic type" << std::endl;
    }
  }
}

bool CegConjecture::inferIteTemplate( unsigned k, Node n, std::map< Node, unsigned >& templ_var_index, std::map< unsigned, unsigned >& templ_injection ){
  if( n.getNumChildren()==0 ){
    std::map< Node, unsigned >::iterator itt = templ_var_index.find( n );
    if( itt!=templ_var_index.end() ){
      unsigned kk = itt->second;
      std::map< unsigned, unsigned >::iterator itti = templ_injection.find( k );
      if( itti==templ_injection.end() ){
        templ_injection[k] = kk;
      }else if( itti->second!=kk ){
        return false;
      }
    }
    return true;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !inferIteTemplate( k, n[i], templ_var_index, templ_injection ) ){
        return false;
      }
    }
  }
  return true;
}

void CegConjecture::initializeGuard(){
  if( isAssigned() ){
    if( !d_syntax_guided ){
      if( d_nsg_guard.isNull() ){
        d_nsg_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
        d_nsg_guard = d_qe->getValuation().ensureLiteral( d_nsg_guard );
        AlwaysAssert( !d_nsg_guard.isNull() );
        d_qe->getOutputChannel().requirePhase( d_nsg_guard, true );
        //add immediate lemma
        Node lem = NodeManager::currentNM()->mkNode( OR, d_nsg_guard.negate(), d_base_inst.negate() );
        Trace("cegqi-lemma") << "Cegqi::Lemma : non-syntax-guided : " << lem << std::endl;
        d_qe->getOutputChannel().lemma( lem );
      }
    }else if( d_ceg_si->d_si_guard.isNull() ){
      std::vector< Node > lems;
      d_ceg_si->getInitialSingleInvLemma( lems );
      for( unsigned i=0; i<lems.size(); i++ ){
        Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation " << i << " : " << lems[i] << std::endl;
        d_qe->getOutputChannel().lemma( lems[i] );
        if( Trace.isOn("cegqi-debug") ){
          Node rlem = Rewriter::rewrite( lems[i] );
          Trace("cegqi-debug") << "...rewritten : " << rlem << std::endl;
        }
      }
    }
    Assert( !getGuard().isNull() );
  }
}
  
Node CegConjecture::getFairnessLiteral( int i ) {
  if( getCegqiFairMode()!=CEGQI_FAIR_NONE ){
    std::map< int, Node >::iterator it = d_lits.find( i );
    if( it==d_lits.end() ){
      Trace("cegqi-engine") << "******* CEGQI : allocate size literal " << i << std::endl;
      Node c = NodeManager::currentNM()->mkConst( Rational( i ) );
      Node lit = NodeManager::currentNM()->mkNode( DT_SYGUS_BOUND, c );
      d_lits[i] = lit;

      Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit, lit.negate() );
      Trace("cegqi-lemma") << "Cegqi::Lemma : Fairness split : " << lem << std::endl;
      d_qe->getOutputChannel().lemma( lem );
      d_qe->getOutputChannel().requirePhase( lit, true );
      return lit;
    }else{
      return it->second;
    }
  }else{
    return Node::null();
  }
}

Node CegConjecture::getGuard() {
  return !d_syntax_guided ? d_nsg_guard : d_ceg_si->d_si_guard;
}

CegqiFairMode CegConjecture::getCegqiFairMode() {
  return isSingleInvocation() ? CEGQI_FAIR_NONE : options::ceGuidedInstFair();
}

bool CegConjecture::isSingleInvocation() const {
  return d_ceg_si->isSingleInvocation();
}

bool CegConjecture::isFullySingleInvocation() {
  return d_ceg_si->isFullySingleInvocation();
}

bool CegConjecture::needsCheck( std::vector< Node >& lem ) {
  if( isSingleInvocation() && !d_ceg_si->needsCheck() ){
    return false;
  }else{
    bool value;
    if( !isSingleInvocation() || isFullySingleInvocation() ){
      Assert( !getGuard().isNull() );
      // non or fully single invocation : look at guard only
      if( d_qe->getValuation().hasSatValue( getGuard(), value ) ) {
        if( !value ){
          Trace("cegqi-engine-debug") << "Conjecture is infeasible." << std::endl;
          return false;
        }
      }else{
        Assert( false );
      }
    }else{
      // not fully single invocation : infeasible if overall specification is infeasible
      Assert( !d_ceg_si->d_full_guard.isNull() );
      if( d_qe->getValuation().hasSatValue( d_ceg_si->d_full_guard, value ) ) {
        if( !value ){
          Trace("cegqi-nsi") << "NSI : found full specification is infeasible." << std::endl;
          return false;
        }else{
          Assert( !d_ceg_si->d_si_guard.isNull() );
          if( d_qe->getValuation().hasSatValue( d_ceg_si->d_si_guard, value ) ) {
            if( !value ){
              if( !d_ceg_si->d_single_inv_exp.isNull() ){
                //this should happen infrequently : only if cegqi determines infeasibility of a false candidate before E-matching does
                Trace("cegqi-nsi") << "NSI : current single invocation lemma was infeasible, block assignment upon which conjecture was based." << std::endl;
                Node l = NodeManager::currentNM()->mkNode( OR, d_ceg_si->d_full_guard.negate(), d_ceg_si->d_single_inv_exp );
                lem.push_back( l );
                d_ceg_si->initializeNextSiConjecture();
              }
              return false;
            }
          }else{
            Assert( false );
          }
        }
      }else{
        Assert( false );
      }
    }
    return true;
  }
}


void CegConjecture::doCegConjectureSingleInvCheck(std::vector< Node >& lems) {
  if( d_ceg_si!=NULL ){
    d_ceg_si->check(lems);
  }
}

bool CegConjecture::needsRefinement() { 
  return !d_ce_sk.empty();
}

void CegConjecture::getConditionalCandidateList( std::vector< Node >& clist, Node curr, bool reqAdd ){
  Assert( options::sygusUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
  if( it!=d_cinfo.end() ){
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        int pstatus = getProgressStatus( curr );
        if( pstatus!=-1 ){
          Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
          //interested in model value for condition and branched variables
          clist.push_back( it->second.d_csol_cond );
          //assume_flat_ITEs
          clist.push_back( it->second.d_csol_var[it->second.d_csol_status] );
          //conditionally get the other branch
          getConditionalCandidateList( clist, it->second.d_csol_var[1-it->second.d_csol_status], false );
          return;
        }else{
          // it is progress-inactive, will not be included
        }
      }
      //otherwise, yet to expand branch
      if( !reqAdd ){
        // if we are not top-level, we can ignore this (it won't be part of solution)
        return;
      }
    }else{
      // a standard variable not handlable by unification
    }
    clist.push_back( curr );
  }
}

void CegConjecture::getCandidateList( std::vector< Node >& clist, bool forceOrig ) {
  if( options::sygusUnifCondSol() && !forceOrig ){
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      getConditionalCandidateList( clist, d_candidates[i], true );
    }
  }else{
    clist.insert( clist.end(), d_candidates.begin(), d_candidates.end() );
  }
}

Node CegConjecture::constructConditionalCandidate( std::map< Node, Node >& cmv, Node curr ) {
  Assert( options::sygusUnifCondSol() );
  std::map< Node, Node >::iterator itc = cmv.find( curr );
  if( itc!=cmv.end() ){
    return itc->second;
  }else{
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
    if( it!=d_cinfo.end() ){
      if( !it->second.d_csol_cond.isNull() ){
        if( it->second.d_csol_status!=-1 ){
          int pstatus = getProgressStatus( curr );
          if( pstatus!=-1 ){
            Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
            Node v_curr = constructConditionalCandidate( cmv, it->second.d_csol_var[it->second.d_csol_status] );
            Node v_next = constructConditionalCandidate( cmv, it->second.d_csol_var[1-it->second.d_csol_status] );
            if( v_next.isNull() ){
              // try taking current branch as a leaf
              return v_curr;
            }else{
              Node v_cond = constructConditionalCandidate( cmv, it->second.d_csol_cond );
              std::vector< Node > args;
              args.push_back( it->second.d_csol_op );
              args.push_back( v_cond );
              args.push_back( it->second.d_csol_status==0 ? v_curr : v_next );
              args.push_back( it->second.d_csol_status==0 ? v_next : v_curr );
              return NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, args );
            }
          }
        }
      }
    }
  }
  return Node::null();
}

bool CegConjecture::constructCandidates( std::vector< Node >& clist, std::vector< Node >& model_values, std::vector< Node >& candidate_values ) {
  Assert( clist.size()==model_values.size() );
  if( options::sygusUnifCondSol() ){
    std::map< Node, Node > cmv;
    for( unsigned i=0; i<clist.size(); i++ ){
      cmv[ clist[i] ] = model_values[i];
    }
    for( unsigned i=0; i<d_candidates.size(); i++ ){
      Node n = constructConditionalCandidate( cmv, d_candidates[i] );
      Trace("cegqi-candidate") << "...constructed conditional candidate " << n << " for " << d_candidates[i] << std::endl;
      candidate_values.push_back( n );
      if( n.isNull() ){
        Assert( false ); //currently should never happen
        return false;
      }
    }
  }else{
    Assert( model_values.size()==d_candidates.size() );
    candidate_values.insert( candidate_values.end(), model_values.begin(), model_values.end() );
  }
  return true;
}

void CegConjecture::doCegConjectureCheck(std::vector< Node >& lems, std::vector< Node >& model_values) {
  std::vector< Node > clist;
  getCandidateList( clist );
  std::vector< Node > c_model_values;
  Trace("cegqi-check") << "CegConjuncture : check, build candidates..." << std::endl;
  if( constructCandidates( clist, model_values, c_model_values ) ){
    Assert( c_model_values.size()==d_candidates.size() );
    if( Trace.isOn("cegqi-check")  ){
      Trace("cegqi-check") << "CegConjuncture : check candidate : " << std::endl;
      for( unsigned i=0; i<c_model_values.size(); i++ ){
        Trace("cegqi-check") << "  " << i << " : " << d_candidates[i] << " -> " << c_model_values[i] << std::endl;
      }
    }
    //must get a counterexample to the value of the current candidate
    Node inst = d_base_inst.substitute( d_candidates.begin(), d_candidates.end(), c_model_values.begin(), c_model_values.end() );
    bool hasActiveConditionalNode = false;
    if( options::sygusUnifCondSol() ){
      //TODO
      hasActiveConditionalNode = true;
    }
    //check whether we will run CEGIS on inner skolem variables
    bool sk_refine = ( !isGround() || d_refine_count==0 || hasActiveConditionalNode );
    if( sk_refine ){
      Assert( d_ce_sk.empty() );
      d_ce_sk.push_back( std::vector< Node >() );
    }
    std::vector< Node > ic;
    ic.push_back( d_assert_quant.negate() );
    std::vector< Node > d;
    CegInstantiation::collectDisjuncts( inst, d );
    Assert( d.size()==d_base_disj.size() );
    //immediately skolemize inner existentials
    for( unsigned i=0; i<d.size(); i++ ){
      Node dr = Rewriter::rewrite( d[i] );
      if( dr.getKind()==NOT && dr[0].getKind()==FORALL ){
        ic.push_back( d_qe->getTermDatabase()->getSkolemizedBody( dr[0] ).negate() );
        if( sk_refine ){
          d_ce_sk.back().push_back( dr[0] );
        }
      }else{
        ic.push_back( dr );
        if( sk_refine ){
          d_ce_sk.back().push_back( Node::null() );
        }
        if( !d_inner_vars_disj[i].empty() ){
          Trace("cegqi-debug") << "*** quantified disjunct : " << d[i] << " simplifies to " << dr << std::endl;
        }
      }
    }
    Node lem = NodeManager::currentNM()->mkNode( OR, ic );
    lem = Rewriter::rewrite( lem );
    lems.push_back( lem );
    recordInstantiation( c_model_values );
  }else{
    Assert( false );
  }
}

Node CegConjecture::getActiveConditional( Node curr ) {
  Assert( options::sygusUnifCondSol() );
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
  Assert( it!=d_cinfo.end() );
  if( !it->second.d_csol_cond.isNull() ){
    if( it->second.d_csol_status==-1 ){
      //yet to branch, this is the one
      return curr;
    }else{
      int pstatus = getProgressStatus( curr );
      if( pstatus==-1 ){
        // it is progress-inactive
        return curr;
      }else{
        Assert( it->second.d_csol_status==0 || it->second.d_csol_status==1 );
        return getActiveConditional( it->second.d_csol_var[1-it->second.d_csol_status] );
      }
    }
  }else{
    //not a conditional
    return curr;
  }
}

void CegConjecture::getContextConditionalNodes( Node curr, Node x, std::vector< Node >& nodes ) {
  if( curr!=x ){
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( curr );
    if( !it->second.d_csol_cond.isNull() ){
      if( it->second.d_csol_status!=-1 ){
        nodes.push_back( curr );
        getContextConditionalNodes( it->second.d_csol_var[1-it->second.d_csol_status], x, nodes );
      }
    }
  }
}

Node CegConjecture::mkConditionalEvalNode( Node c, std::vector< Node >& args ) {
  Assert( !c.isNull() );
  std::vector< Node > condc;
  //get evaluator
  Assert( c.getType().isDatatype() );
  const Datatype& cd = ((DatatypeType)c.getType().toType()).getDatatype();
  Assert( cd.isSygus() );
  condc.push_back( Node::fromExpr( cd.getSygusEvaluationFunc() ) );
  condc.push_back( c );
  for( unsigned a=0; a<args.size(); a++ ){
    condc.push_back( args[a] );
  }
  return NodeManager::currentNM()->mkNode( kind::APPLY_UF, condc );
}

Node CegConjecture::mkConditionalNode( Node v, std::vector< Node >& args, unsigned eindex ) {
  std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
  if( it!=d_cinfo.end() ){
    Assert( eindex<=2 );
    Node en = eindex==0 ? it->second.d_csol_cond : it->second.d_csol_var[eindex-1];
    if( !en.isNull() ){
      Node ret = mkConditionalEvalNode( en, args );
      //consider template
      std::map< unsigned, Node >::iterator itt = it->second.d_template.find( eindex );
      if( itt!=it->second.d_template.end() ){
        Assert( it->second.d_template_arg.find( eindex )!=it->second.d_template_arg.end() );
        TNode var = it->second.d_template_arg[eindex];
        TNode subs = ret;
        Node rret = itt->second.substitute( var, subs );
        ret = rret;
      }
      return ret;
    }
  }
  Assert( false );
  return Node::null();
}

Node CegConjecture::mkConditional( Node v, std::vector< Node >& args, bool pol ) {
  Node ret = mkConditionalNode( v, args, 0 );
  if( !pol ){
    ret = ret.negate();
  }
  return ret;
}
  
Node CegConjecture::purifyConditionalEvaluations( Node n, std::map< Node, Node >& csol_active, std::map< Node, Node >& psubs, std::map< Node, Node >& visited ){
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }else{
    Node ret;
    if( n.getKind()==APPLY_UF ){
      std::map< Node, Node >::iterator itc = csol_active.find( n[0] );
      if( itc!=csol_active.end() ){
        //purify it with a variable
        ret = NodeManager::currentNM()->mkSkolem( "y", n.getType(), "purification variable for sygus conditional solution" );
        psubs[n] = ret;
      }
    }
    if( ret.isNull() ){
      ret = n;
      if( n.getNumChildren()>0 ){
        std::vector< Node > children;
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.push_back( n.getOperator() );
        }
        bool childChanged = false;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = purifyConditionalEvaluations( n[i], csol_active, psubs, visited );
          childChanged = childChanged || nc!=n[i];
          children.push_back( nc );
        }
        if( childChanged ){
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
    }
    visited[n] = ret;
    return ret;
  }
}
        
void CegConjecture::doCegConjectureRefine( std::vector< Node >& lems ){
  Assert( lems.empty() );
  Assert( d_ce_sk.size()==1 );

  //first, make skolem substitution
  Trace("cegqi-refine") << "doCegConjectureRefine : construct skolem substitution..." << std::endl;
  std::vector< Node > sk_vars;
  std::vector< Node > sk_subs;
  //collect the substitution over all disjuncts
  for( unsigned k=0; k<d_ce_sk[0].size(); k++ ){
    Node ce_q = d_ce_sk[0][k];
    if( !ce_q.isNull() ){
      Assert( !d_inner_vars_disj[k].empty() );
      Assert( d_inner_vars_disj[k].size()==d_qe->getTermDatabase()->d_skolem_constants[ce_q].size() );
      std::vector< Node > model_values;
      getModelValues( d_qe->getTermDatabase()->d_skolem_constants[ce_q], model_values );
      sk_vars.insert( sk_vars.end(), d_inner_vars_disj[k].begin(), d_inner_vars_disj[k].end() );
      sk_subs.insert( sk_subs.end(), model_values.begin(), model_values.end() );
    }else{
      if( !d_inner_vars_disj[k].empty() ){
        //denegrate case : quantified disjunct was trivially true and does not need to be refined
        //add trivial substitution (in case we need substitution for previous cex's)
        for( unsigned i=0; i<d_inner_vars_disj[k].size(); i++ ){
          sk_vars.push_back( d_inner_vars_disj[k][i] );
          sk_subs.push_back( getModelValue( d_inner_vars_disj[k][i] ) ); // will return dummy value
        }
      }
    }
  }
  
  std::map< Node, Node > csol_active;
  std::map< Node, std::vector< Node > > csol_ccond_nodes;
  std::map< Node, std::map< Node, bool > > csol_cpol;    
  
  //for conditional evaluation
  std::map< Node, Node > psubs_visited;
  std::map< Node, Node > psubs;
  std::vector< Node > lem_c;
  Assert( d_ce_sk[0].size()==d_base_disj.size() );
  std::vector< Node > inst_cond_c;
  Trace("cegqi-refine") << "doCegConjectureRefine : Construct refinement lemma..." << std::endl;
  for( unsigned k=0; k<d_ce_sk[0].size(); k++ ){
    Node ce_q = d_ce_sk[0][k];
    Trace("cegqi-refine-debug") << "  For counterexample point, disjunct " << k << " : " << ce_q << " " << d_base_disj[k] << std::endl;
    Node c_disj;
    if( !ce_q.isNull() ){
      Assert( d_base_disj[k].getKind()==kind::NOT && d_base_disj[k][0].getKind()==kind::FORALL );
      c_disj = d_base_disj[k][0][1];
    }else{
      if( d_inner_vars_disj[k].empty() ){
        c_disj = d_base_disj[k].negate();
      }else{
        //denegrate case : quantified disjunct was trivially true and does not need to be refined
        Trace("cegqi-refine-debug") << "*** skip " << d_base_disj[k] << std::endl;
      }
    }
    if( !c_disj.isNull() ){
      //compute the body, inst_cond
      //standard CEGIS refinement : plug in values, assert that d_candidates must satisfy entire specification
      lem_c.push_back( c_disj );
    }
  }
  Assert( sk_vars.size()==sk_subs.size() );
  //add conditional correctness assumptions
  std::vector< Node > psubs_cond_ant;
  std::vector< Node > psubs_cond_conc;
  std::map< Node, std::vector< Node > > psubs_apply;
  std::vector< Node > paux_vars;
  Assert( psubs.empty() );
  
  Node base_lem = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( AND, lem_c );
  
  Trace("cegqi-refine") << "doCegConjectureRefine : construct and finalize lemmas..." << std::endl;
  
  Node lem = base_lem;
  
  base_lem = base_lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
  base_lem = Rewriter::rewrite( base_lem );
  d_refinement_lemmas_base.push_back( base_lem );
  
  lem = NodeManager::currentNM()->mkNode( OR, getGuard().negate(), lem );
  
  lem = lem.substitute( sk_vars.begin(), sk_vars.end(), sk_subs.begin(), sk_subs.end() );
  lem = Rewriter::rewrite( lem );
  d_refinement_lemmas.push_back( lem );
  lems.push_back( lem );

  d_ce_sk.clear();
}

void CegConjecture::preregisterConjecture( Node q ) {
  d_ceg_si->preregisterConjecture( q );
}

void CegConjecture::getModelValues( std::vector< Node >& n, std::vector< Node >& v ) {
  Trace("cegqi-engine") << "  * Value is : ";
  for( unsigned i=0; i<n.size(); i++ ){
    Node nv = getModelValue( n[i] );
    v.push_back( nv );
    if( Trace.isOn("cegqi-engine") ){
      TypeNode tn = nv.getType();
      Trace("cegqi-engine") << n[i] << " -> ";
      std::stringstream ss;
      std::vector< Node > lvs;
      TermDbSygus::printSygusTerm( ss, nv, lvs );
      Trace("cegqi-engine") << ss.str() << " ";
    }
    Assert( !nv.isNull() );
  }
  Trace("cegqi-engine") << std::endl;
}

Node CegConjecture::getModelValue( Node n ) {
  Trace("cegqi-mv") << "getModelValue for : " << n << std::endl;
  return d_qe->getModel()->getValue( n );
}

void CegConjecture::debugPrint( const char * c ) {
  Trace(c) << "Synthesis conjecture : " << d_quant << std::endl;
  Trace(c) << "  * Candidate program/output symbol : ";
  for( unsigned i=0; i<d_candidates.size(); i++ ){
    Trace(c) << d_candidates[i] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "  * Candidate ce skolems : ";
  for( unsigned i=0; i<d_ce_sk.size(); i++ ){
    Trace(c) << d_ce_sk[i] << " ";
  }
}

int CegConjecture::getProgressStatus( Node v ) {

  return -2;
}

Node CegConjecture::getNextDecisionRequestConditional( Node v, unsigned& priority ) {

  return Node::null();
}

Node CegConjecture::getNextDecisionRequest( unsigned& priority ) {
  if( options::sygusUnifCondSolNew() ){

  }
  return Node::null();
}

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( qe, qe->getSatContext() );
  d_last_inst_si = false;
}

CegInstantiation::~CegInstantiation(){ 
  delete d_conj;
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

unsigned CegInstantiation::needsModel( Theory::Effort e ) {
  return d_conj->getCegConjectureSingleInv()->isSingleInvocation()
      ? QuantifiersEngine::QEFFORT_STANDARD : QuantifiersEngine::QEFFORT_MODEL;
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  unsigned echeck = d_conj->getCegConjectureSingleInv()->isSingleInvocation() ?
      QuantifiersEngine::QEFFORT_STANDARD : QuantifiersEngine::QEFFORT_MODEL;
  if( quant_e==echeck ){
    Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---" << std::endl;
    Trace("cegqi-engine-debug") << std::endl;
    bool active = false;
    bool value;
    if( d_quantEngine->getValuation().hasSatValue( d_conj->d_assert_quant, value ) ) {
      active = value;
    }else{
      Trace("cegqi-engine-debug") << "...no value for quantified formula." << std::endl;
    }
    Trace("cegqi-engine-debug") << "Current conjecture status : active : " << active << std::endl;
    std::vector< Node > lem;
    if( active && d_conj->needsCheck( lem ) ){
      checkCegConjecture( d_conj );
    }else{
      Trace("cegqi-engine-debug") << "...does not need check." << std::endl;
      for( unsigned i=0; i<lem.size(); i++ ){
        Trace("cegqi-lemma") << "Cegqi::Lemma : check lemma : " << lem[i] << std::endl;
        d_quantEngine->addLemma( lem[i] );
      }
    }
    Trace("cegqi-engine") << "Finished Counterexample Guided Instantiation engine." << std::endl;
  }
}

void CegInstantiation::preRegisterQuantifier( Node q ) {
/*
  if( options::sygusDirectEval() ){
    if( q.getNumChildren()==3 && q[2].getKind()==INST_PATTERN_LIST && q[2][0].getKind()==INST_PATTERN ){  
      //check whether it is an evaluation axiom
      Node pat = q[2][0][0];
      if( pat.getKind()==APPLY_UF ){
        TypeNode tn = pat[0].getType();
        if( tn.isDatatype() ){
          const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
          if( dt.isSygus() ){
            //do unfolding if it induces Boolean structure, 
            //do direct evaluation if it does not induce Boolean structure,
            //  the reasoning is unfolding over these terms does not lead to helpful conflict analysis, and introduces many shared terms
            bool directEval = true;
            TypeNode ptn = pat.getType();
            if( ptn.isBoolean() ){
              directEval = false;
            }else{
              unsigned cindex = Datatype::indexOf(pat[0].getOperator().toExpr() );
              Node base = d_quantEngine->getTermDatabaseSygus()->getGenericBase( tn, dt, cindex );
              Trace("cegqi-debug") << "Generic base term for " << pat[0] << " is " << base << std::endl;
              if( base.getKind()==ITE ){
                directEval = false;
              }
            }
            if( directEval ){
              //take ownership of this quantified formula (will use direct evaluation instead of unfolding instantiation)
              d_quantEngine->setOwner( q, this );
              d_eval_axioms[q] = true;
            }
          }
        }
      }
    }
  } 
  */ 
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==this && d_eval_axioms.find( q )==d_eval_axioms.end() ){
    if( !d_conj->isAssigned() ){
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      d_conj->assign( q );
    }else{
      Assert( d_conj->d_quant==q );
    }
  }else{
    Trace("cegqi-debug") << "Register quantifier : " << q << std::endl;
  }
}

void CegInstantiation::assertNode( Node n ) {
}

Node CegInstantiation::getNextDecisionRequest( unsigned& priority ) {
  //enforce fairness
  if( d_conj->isAssigned() ){
    d_conj->initializeGuard();
    // 
    std::vector< Node > req_dec;
    const CegConjectureSingleInv* ceg_si = d_conj->getCegConjectureSingleInv();
    if( ! ceg_si->d_full_guard.isNull() ){
      req_dec.push_back( ceg_si->d_full_guard );
    }
    //must decide ns guard before s guard
    if( !ceg_si->d_ns_guard.isNull() ){
      req_dec.push_back( ceg_si->d_ns_guard );
    }
    req_dec.push_back( d_conj->getGuard() );
    for( unsigned i=0; i<req_dec.size(); i++ ){
      bool value;
      if( !d_quantEngine->getValuation().hasSatValue( req_dec[i], value ) ) {
        Trace("cegqi-debug") << "CEGQI : Decide next on : " << req_dec[i] << "..." << std::endl;
        priority = 0;
        return req_dec[i];
      }else{
        Trace("cegqi-debug2") << "CEGQI : " << req_dec[i] << " already has value " << value << std::endl;
      }
    }
    
    //ask the conjecture directly
    Node lit = d_conj->getNextDecisionRequest( priority );
    if( !lit.isNull() ){
      return lit;
    }

    lit = d_conj->getFairnessLiteral( d_conj->getCurrentTermSize() );
    if( !lit.isNull() ){
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( lit, value ) ) {
        if( !value ){
          d_conj->incrementCurrentTermSize();
          lit = d_conj->getFairnessLiteral( d_conj->getCurrentTermSize() );
          Assert( !lit.isNull() );
          Trace("cegqi-debug") << "CEGQI : Decide on next lit : " << lit << "..." << std::endl;
          priority = 1;
          return lit;
        }
      }else{
        Trace("cegqi-debug") << "CEGQI : Decide on current lit : " << lit << "..." << std::endl;
        priority = 1;
        return lit;
      }
    }
  }

  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  Node q = conj->d_quant;
  Node aq = conj->d_assert_quant;
  if( Trace.isOn("cegqi-engine-debug") ){
    conj->debugPrint("cegqi-engine-debug");
    Trace("cegqi-engine-debug") << std::endl;
  }
  if( conj->getCegqiFairMode()!=CEGQI_FAIR_NONE ){
    Trace("cegqi-engine") << "  * Current term size : " << conj->getCurrentTermSize() << std::endl;
  }  

  if( !conj->needsRefinement() ){
    if( conj->d_syntax_guided ){
      std::vector< Node > clems;
      conj->doCegConjectureSingleInvCheck( clems );
      if( !clems.empty() ){
        d_last_inst_si = true;
        for( unsigned j=0; j<clems.size(); j++ ){
          Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation instantiation : " << clems[j] << std::endl;
          d_quantEngine->addLemma( clems[j] );
        }
        d_statistics.d_cegqi_si_lemmas += clems.size();
        Trace("cegqi-engine") << "  ...try single invocation." << std::endl;
        return;
      }
      //ignore return value here
      std::vector< Node > clist;
      conj->getCandidateList( clist );
      std::vector< Node > model_values;
      conj->getModelValues( clist, model_values );
      if( options::sygusDirectEval() ){
        bool addedEvalLemmas = false;
        if( options::sygusCRefEval() ){
          Trace("cegqi-debug") << "Do cref evaluation..." << std::endl;
          // see if any refinement lemma is refuted by evaluation
          std::vector< Node > cre_lems;
          getCRefEvaluationLemmas( conj, clist, model_values, cre_lems );
          if( !cre_lems.empty() ){
            Trace("cegqi-engine") << "  *** Do conjecture refinement evaluation..." << std::endl;
            for( unsigned j=0; j<cre_lems.size(); j++ ){
              Node lem = cre_lems[j];
              if( d_quantEngine->addLemma( lem ) ){
                Trace("cegqi-lemma") << "Cegqi::Lemma : cref evaluation : " << lem << std::endl;
                addedEvalLemmas = true;
              }
            }
            if( addedEvalLemmas ){
              //return;
            }
          }
        }
        Trace("cegqi-debug") << "Do direct evaluation..." << std::endl;
        std::vector< Node > eager_terms; 
        std::vector< Node > eager_vals; 
        std::vector< Node > eager_exps;
        for( unsigned j=0; j<clist.size(); j++ ){
          Trace("cegqi-debug") << "  register " << clist[j] << " -> " << model_values[j] << std::endl;
          d_quantEngine->getTermDatabaseSygus()->registerModelValue( clist[j], model_values[j], eager_terms, eager_vals, eager_exps );
        }
        Trace("cegqi-debug") << "...produced " << eager_terms.size()  << " eager evaluation lemmas." << std::endl;
        if( !eager_terms.empty() ){
          Trace("cegqi-engine") << "  *** Do direct evaluation..." << std::endl;
          for( unsigned j=0; j<eager_terms.size(); j++ ){
            Node lem = NodeManager::currentNM()->mkNode( kind::OR, eager_exps[j].negate(), eager_terms[j].eqNode( eager_vals[j] ) );
            if( d_quantEngine->getTheoryEngine()->isTheoryEnabled(THEORY_BV) ){
              //FIXME: hack to incorporate hacks from BV for division by zero
              lem = bv::TheoryBVRewriter::eliminateBVSDiv( lem );
            }
            if( d_quantEngine->addLemma( lem ) ){
              Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation : " << lem << std::endl;
              addedEvalLemmas = true;
            }
          }
        }
        if( addedEvalLemmas ){
          return;
        }
      }
      
      Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
      std::vector< Node > cclems;
      conj->doCegConjectureCheck( cclems, model_values );
      bool addedLemma = false;
      for( unsigned i=0; i<cclems.size(); i++ ){
        Node lem = cclems[i];
        d_last_inst_si = false;
        //eagerly unfold applications of evaluation function
        if( options::sygusDirectEval() ){
          Trace("cegqi-eager") << "pre-unfold counterexample : " << lem << std::endl;
          std::map< Node, Node > visited_n;
          lem = getEagerUnfold( lem, visited_n );
        }
        Trace("cegqi-lemma") << "Cegqi::Lemma : counterexample : " << lem << std::endl;
        if( d_quantEngine->addLemma( lem ) ){
          ++(d_statistics.d_cegqi_lemmas_ce);
          addedLemma = true;
        }else{
          //this may happen if we eagerly unfold, simplify to true
          if( !options::sygusDirectEval() ){
            Trace("cegqi-warn") << "  ...FAILED to add candidate!" << std::endl;
          }else{
            Trace("cegqi-engine-debug") << "  ...FAILED to add candidate!" << std::endl;
          }
        }
      }
      if( addedLemma ){
        Trace("cegqi-engine") << "  ...check for counterexample." << std::endl;
      }else{
        if( conj->needsRefinement() ){
          //immediately go to refine candidate
          checkCegConjecture( conj );
          return;
        }
      } 
    }else{
      Assert( aq==q );
      std::vector< Node > model_terms;
      std::vector< Node > clist;
      conj->getCandidateList( clist, true );
      Assert( clist.size()==q[0].getNumChildren() );
      conj->getModelValues( clist, model_terms );
      if( d_quantEngine->addInstantiation( q, model_terms ) ){
        conj->recordInstantiation( model_terms );
      }else{
        Assert( false );
      }
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    std::vector< Node > rlems;
    conj->doCegConjectureRefine( rlems );
    bool addedLemma = false;
    for( unsigned i=0; i<rlems.size(); i++ ){
      Node lem = rlems[i];
      Trace("cegqi-lemma") << "Cegqi::Lemma : candidate refinement : " << lem << std::endl;
      bool res = d_quantEngine->addLemma( lem );
      if( res ){
        ++(d_statistics.d_cegqi_lemmas_refine);
        conj->d_refine_count++;
        addedLemma = true;
      }else{
        Trace("cegqi-warn") << "  ...FAILED to add refinement!" << std::endl;
      }
    }
    if( addedLemma ){
      Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
    }
  }
}

void CegInstantiation::getCRefEvaluationLemmas( CegConjecture * conj, std::vector< Node >& vs, std::vector< Node >& ms, std::vector< Node >& lems ) {
  if( conj->getNumRefinementLemmas()>0 ){
    Assert( vs.size()==ms.size() );
    std::map< Node, Node > vtm;
    for( unsigned i=0; i<vs.size(); i++ ){
      vtm[vs[i]] = ms[i];
    }

    for( unsigned i=0; i<conj->getNumRefinementLemmas(); i++ ){
      Node lem;
      std::map< Node, Node > visited;
      std::map< Node, std::vector< Node > > exp;
      lem = conj->getRefinementBaseLemma( i );
      if( !lem.isNull() ){
        std::vector< Node > lem_conj;
        //break into conjunctions
        if( lem.getKind()==kind::AND ){
          for( unsigned i=0; i<lem.getNumChildren(); i++ ){
            lem_conj.push_back( lem[i] );
          }
        }else{
          lem_conj.push_back( lem );
        }
        for( unsigned j=0; j<lem_conj.size(); j++ ){
          Node lemc = lem_conj[j];
          Trace("sygus-cref-eval") << "Check refinement lemma conjunct " << lemc << " against current model." << std::endl;
          Node elem = d_quantEngine->getTermDatabaseSygus()->crefEvaluate( lemc, vtm, visited, exp );
          Trace("sygus-cref-eval") << "...evaluated to " << elem << ", exp size = " << exp[lemc].size() << std::endl;
          if( !elem.isNull() && elem==d_quantEngine->getTermDatabase()->d_false ){
            elem = conj->getGuard().negate();
            Node cre_lem;
            if( !exp[lemc].empty() ){
              Node en = exp[lemc].size()==1 ? exp[lemc][0] : NodeManager::currentNM()->mkNode( kind::AND, exp[lemc] );
              cre_lem = NodeManager::currentNM()->mkNode( kind::OR, en.negate(), elem );
            }else{
              cre_lem = elem;
            }
            if( std::find( lems.begin(), lems.end(), cre_lem )==lems.end() ){
              Trace("sygus-cref-eval") << "...produced lemma : " << cre_lem << std::endl;
              lems.push_back( cre_lem );
            }
          }
        }
      }
    }
  }
}


Node CegInstantiation::getEagerUnfold( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv==visited.end() ){
    Trace("cegqi-eager-debug") << "getEagerUnfold " << n << std::endl;
    Node ret;
    if( n.getKind()==APPLY_UF ){
      TypeNode tn = n[0].getType();
      Trace("cegqi-eager-debug") << "check " << n[0].getType() << std::endl;
      if( tn.isDatatype() ){
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        if( dt.isSygus() ){ 
          Trace("cegqi-eager") << "Unfold eager : " << n << std::endl;
          Node bTerm = d_quantEngine->getTermDatabaseSygus()->sygusToBuiltin( n[0], tn );
          Trace("cegqi-eager") << "Built-in term : " << bTerm << std::endl;
          std::vector< Node > vars;
          std::vector< Node > subs;
          Node var_list = Node::fromExpr( dt.getSygusVarList() );
          Assert( var_list.getNumChildren()+1==n.getNumChildren() );
          for( unsigned j=0; j<var_list.getNumChildren(); j++ ){
            vars.push_back( var_list[j] );
          }
          for( unsigned j=1; j<n.getNumChildren(); j++ ){
            Node nc = getEagerUnfold( n[j], visited );
            subs.push_back( nc );
            Assert( subs[j-1].getType()==var_list[j-1].getType() );
          }
          Assert( vars.size()==subs.size() );
          bTerm = bTerm.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
          Trace("cegqi-eager") << "Built-in term after subs : " << bTerm << std::endl;
          Trace("cegqi-eager-debug") << "Types : " << bTerm.getType() << " " << n.getType() << std::endl;
          Assert( n.getType()==bTerm.getType() );
          ret = bTerm; 
        }
      }
    }
    if( ret.isNull() ){
      if( n.getKind()!=FORALL ){
        bool childChanged = false;
        std::vector< Node > children;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = getEagerUnfold( n[i], visited );
          childChanged = childChanged || n[i]!=nc;
          children.push_back( nc );
        }
        if( childChanged ){
          if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
            children.insert( children.begin(), n.getOperator() );
          }
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
      if( ret.isNull() ){
        ret = n;
      }
    }
    visited[n] = ret;
    return ret;
  }else{
    return itv->second;
  }
}

void CegInstantiation::printSynthSolution( std::ostream& out ) {
  if( d_conj->isAssigned() ){
    Trace("cegqi-debug") << "Printing synth solution..." << std::endl;
    //if( !(Trace.isOn("cegqi-stats")) ){
    //  out << "Solution:" << std::endl;
    //}
    for( unsigned i=0; i<d_conj->d_quant[0].getNumChildren(); i++ ){
      Node prog = d_conj->d_quant[0][i];
      Trace("cegqi-debug") << "  print solution for " << prog << std::endl;
      std::stringstream ss;
      ss << prog;
      std::string f(ss.str());
      f.erase(f.begin());
      TypeNode tn = prog.getType();
      Assert( tn.isDatatype() );
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Assert( dt.isSygus() );
      //get the solution
      Node sol;
      int status = -1;
      if( d_last_inst_si ){
        Assert( d_conj->getCegConjectureSingleInv() != NULL );
        sol = d_conj->getSingleInvocationSolution( i, tn, status );
        sol = sol.getKind()==LAMBDA ? sol[1] : sol;
      }else{
        Node cprog = d_conj->getCandidate( i );
        if( !d_conj->d_cinfo[cprog].d_inst.empty() ){
          sol = d_conj->d_cinfo[cprog].d_inst.back();
          // Check if this was based on a template, if so, we must do
          // Reconstruction
          if( d_conj->d_assert_quant!=d_conj->d_quant ){
            Node sygus_sol = sol;
            Trace("cegqi-inv") << "Sygus version of solution is : " << sol
                               << ", type : " << sol.getType() << std::endl;
            std::vector< Node > subs;
            Expr svl = dt.getSygusVarList();
            for( unsigned j=0; j<svl.getNumChildren(); j++ ){
              subs.push_back( Node::fromExpr( svl[j] ) );
            }
            bool templIsPost = false;
            Node templ;
            if( options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_PRE ){
              const CegConjectureSingleInv* ceg_si = d_conj->getCegConjectureSingleInv();
              if(ceg_si->d_trans_pre.find( prog ) != ceg_si->d_trans_pre.end()){
                templ = ceg_si->getTransPre(prog);
                templIsPost = false;
              }
            }else if(options::sygusInvTemplMode() == SYGUS_INV_TEMPL_MODE_POST){
              const CegConjectureSingleInv* ceg_si = d_conj->getCegConjectureSingleInv();
              if(ceg_si->d_trans_post.find(prog) != ceg_si->d_trans_post.end()){
                templ = ceg_si->getTransPost(prog);
                templIsPost = true;
              }
            }
            Trace("cegqi-inv") << "Template is " << templ << std::endl;
            if( !templ.isNull() ){
              std::vector<Node>& templ_vars = d_conj->getProgTempVars(prog);
              std::vector< Node > vars;
              vars.insert( vars.end(), templ_vars.begin(), templ_vars.end() );
              Node vl = Node::fromExpr( dt.getSygusVarList() );
              Assert(vars.size() == subs.size());
              if( Trace.isOn("cegqi-inv-debug") ){
                for( unsigned j=0; j<vars.size(); j++ ){
                  Trace("cegqi-inv-debug") << "  subs : " << vars[j] << " -> " << subs[j] << std::endl;
                }
              }
              //apply the substitution to the template
              templ = templ.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
              TermDbSygus* sygusDb = getTermDatabase()->getTermDatabaseSygus();
              sol = sygusDb->sygusToBuiltin( sol, sol.getType() );
              Trace("cegqi-inv") << "Builtin version of solution is : "
                                 << sol << ", type : " << sol.getType()
                                 << std::endl;
              sol = NodeManager::currentNM()->mkNode( templIsPost ? AND : OR, sol, templ );
            }
            if( sol==sygus_sol ){
              sol = sygus_sol;
              status = 1;
            }else{
              Trace("cegqi-inv-debug") << "With template : " << sol << std::endl;
              sol = Rewriter::rewrite( sol );
              Trace("cegqi-inv-debug") << "Simplified : " << sol << std::endl;
              sol = d_conj->reconstructToSyntaxSingleInvocation(sol, tn, status);
              sol = sol.getKind()==LAMBDA ? sol[1] : sol;
            }
          }else{
            status = 1;
          }
        }else{
          Trace("cegqi-warn") << "WARNING : No recorded instantiations for syntax-guided solution!" << std::endl;
        }
      }
      if( !(Trace.isOn("cegqi-stats")) ){
        out << "(define-fun " << f << " ";
        if( dt.getSygusVarList().isNull() ){
          out << "() ";
        }else{
          out << dt.getSygusVarList() << " ";
        }
        out << dt.getSygusType() << " ";
        if( status==0 ){
          out << sol;
        }else{
          if( sol.isNull() ){
            out << "?";
          }else{
            std::vector< Node > lvs;
            TermDbSygus::printSygusTerm( out, sol, lvs );
          }
        }
        out << ")" << std::endl;
      }
    }
  }else{
    Assert( false );
  }
}

void CegInstantiation::collectDisjuncts( Node n, std::vector< Node >& d ) {
  if( n.getKind()==OR ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectDisjuncts( n[i], d );
    }
  }else{
    d.push_back( n );
  }
}

void CegInstantiation::preregisterAssertion( Node n ) {
  //check if it sygus conjecture
  if( TermDb::isSygusConjecture( n ) ){
    //this is a sygus conjecture
    Trace("cegqi") << "Preregister sygus conjecture : " << n << std::endl;
    d_conj->preregisterConjecture( n );
  }
}

CegInstantiation::Statistics::Statistics():
  d_cegqi_lemmas_ce("CegInstantiation::cegqi_lemmas_ce", 0),
  d_cegqi_lemmas_refine("CegInstantiation::cegqi_lemmas_refine", 0),
  d_cegqi_si_lemmas("CegInstantiation::cegqi_lemmas_si", 0)
{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
}

CegInstantiation::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
