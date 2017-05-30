/*********************                                                        */
/*! \file theory_strings_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/

#include "theory/strings/theory_strings_rewriter.h"

#include <stdint.h>

#include "options/strings_options.h"
#include "smt/logic_exception.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

Node TheoryStringsRewriter::simpleRegexpConsume( std::vector< Node >& mchildren, std::vector< Node >& children, int dir ){
  unsigned tmin = dir<0 ? 0 : dir;
  unsigned tmax = dir<0 ? 1 : dir;
  //try to remove off front and back
  for( unsigned t=0; t<2; t++ ){
    if( tmin<=t && t<=tmax ){
      bool do_next = true;
      while( !children.empty() && !mchildren.empty() && do_next ){
        do_next = false;
        Node xc = mchildren[mchildren.size()-1];
        Node rc = children[children.size()-1];
        Assert( rc.getKind()!=kind::REGEXP_CONCAT );
        Assert( xc.getKind()!=kind::STRING_CONCAT );
        if( rc.getKind() == kind::STRING_TO_REGEXP ){
          if( xc==rc[0] ){
            children.pop_back();
            mchildren.pop_back();
            do_next = true;
          }else if( xc.isConst() && rc[0].isConst() ){
            //split the constant
            int index;
            Node s = splitConstant( xc, rc[0], index, t==0 );
            Trace("regexp-ext-rewrite-debug") << "CRE: Regexp const split : " << xc << " " << rc[0] << " -> " << s << " " << index << " " << t << std::endl;
            if( s.isNull() ){
              return NodeManager::currentNM()->mkConst( false );
            }else{
              children.pop_back();
              mchildren.pop_back();
              if( index==0 ){
                mchildren.push_back( s );
              }else{
                children.push_back( s );
              }
            }
            do_next = true;
          }
        }else if( xc.isConst() ){
          //check for constants
          CVC4::String s = xc.getConst<String>();
          Assert( s.size()>0 );
          if( rc.getKind() == kind::REGEXP_RANGE || rc.getKind()==kind::REGEXP_SIGMA ){
            CVC4::String ss( t==0 ? s.getLastChar() : s.getFirstChar() );
            if( testConstStringInRegExp( ss, 0, rc ) ){
              //strip off one character
              mchildren.pop_back();
              if( s.size()>1 ){
                if( t==0 ){
                  mchildren.push_back( NodeManager::currentNM()->mkConst(s.substr( 0, s.size()-1 )) );
                }else{
                  mchildren.push_back( NodeManager::currentNM()->mkConst(s.substr( 1 )) );
                }
              }
              children.pop_back();
              do_next = true;
            }else{
              return NodeManager::currentNM()->mkConst( false );
            }
          }else if( rc.getKind()==kind::REGEXP_INTER || rc.getKind()==kind::REGEXP_UNION ){
            //see if any/each child does not work
            bool result_valid = true;
            Node result;
            Node emp_s = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
            for( unsigned i=0; i<rc.getNumChildren(); i++ ){
              std::vector< Node > mchildren_s;
              std::vector< Node > children_s;
              mchildren_s.push_back( xc );
              getConcat( rc[i], children_s );
              Node ret = simpleRegexpConsume( mchildren_s, children_s, t );
              if( !ret.isNull() ){
                // one conjunct cannot be satisfied, return false
                if( rc.getKind()==kind::REGEXP_INTER ){
                  return ret;
                }
              }else{
                if( children_s.empty() ){
                  //if we were able to fully consume, store the result
                  Assert( mchildren_s.size()<=1 );
                  if( mchildren_s.empty() ){
                    mchildren_s.push_back( emp_s );
                  }
                  if( result.isNull() ){
                    result = mchildren_s[0];
                  }else if( result!=mchildren_s[0] ){
                    result_valid = false;
                  }
                }else{
                  result_valid = false;
                }
              }
            }
            if( result_valid ){
              if( result.isNull() ){
                //all disjuncts cannot be satisfied, return false
                Assert( rc.getKind()==kind::REGEXP_UNION );
                return NodeManager::currentNM()->mkConst( false );
              }else{
                //all branches led to the same result
                children.pop_back();
                mchildren.pop_back();
                if( result!=emp_s ){
                  mchildren.push_back( result );
                }
                do_next = true;
              }
            }
          }else if( rc.getKind()==kind::REGEXP_STAR ){
            //check if there is no way that this star can be unrolled even once
            std::vector< Node > mchildren_s;
            mchildren_s.insert( mchildren_s.end(), mchildren.begin(), mchildren.end() );
            if( t==1 ){
              std::reverse( mchildren_s.begin(), mchildren_s.end() );
            }
            std::vector< Node > children_s;
            getConcat( rc[0], children_s );
            Node ret = simpleRegexpConsume( mchildren_s, children_s, t );
            if( !ret.isNull() ){
              Trace("regexp-ext-rewrite-debug") << "CRE : regexp star infeasable " << xc << " " << rc << std::endl;
              children.pop_back();
              if( children.empty() ){
                return NodeManager::currentNM()->mkConst( false );
              }else{
                do_next = true;
              }
            }else{
              if( children_s.empty() ){
                //check if beyond this, we can't do it or there is nothing left, if so, repeat
                bool can_skip = false;
                if( children.size()>1 ){
                  std::vector< Node > mchildren_ss;
                  mchildren_ss.insert( mchildren_ss.end(), mchildren.begin(), mchildren.end() );
                  std::vector< Node > children_ss;
                  children_ss.insert( children_ss.end(), children.begin(), children.end()-1 );
                  if( t==1 ){
                    std::reverse( mchildren_ss.begin(), mchildren_ss.end() );
                    std::reverse( children_ss.begin(), children_ss.end() );
                  }
                  Node ret = simpleRegexpConsume( mchildren_ss, children_ss, t );
                  if( ret.isNull() ){
                    can_skip = true;
                  }
                }
                if( !can_skip ){
                  //take the result of fully consuming once
                  if( t==1 ){
                    std::reverse( mchildren_s.begin(), mchildren_s.end() );
                  }
                  mchildren.clear();
                  mchildren.insert( mchildren.end(), mchildren_s.begin(), mchildren_s.end() );
                  do_next = true;
                }else{
                  Trace("regexp-ext-rewrite-debug") << "CRE : can skip " << rc << " from " << xc << std::endl;
                }
              }
            }
          }
        }
        if( !do_next ){
          Trace("regexp-ext-rewrite") << "Cannot consume : " << xc << " " << rc << std::endl;
        }
      }
    }
    if( dir!=0 ){
      std::reverse( children.begin(), children.end() );
      std::reverse( mchildren.begin(), mchildren.end() );
    }
  }
  return Node::null();
}

Node TheoryStringsRewriter::rewriteConcatString( TNode node ) {
  Trace("strings-prerewrite") << "Strings::rewriteConcatString start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  for(unsigned int i=0; i<node.getNumChildren(); ++i) {
    Node tmpNode = node[i];
    if(node[i].getKind() == kind::STRING_CONCAT) {
      tmpNode = rewriteConcatString(node[i]);
      if(tmpNode.getKind() == kind::STRING_CONCAT) {
        unsigned j=0;
        if(!preNode.isNull()) {
          if(tmpNode[0].isConst()) {
            preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode[0].getConst<String>() ) );
            node_vec.push_back( preNode );
          } else {
            node_vec.push_back( preNode );
            node_vec.push_back( tmpNode[0] );
          }
          preNode = Node::null();
          ++j;
        }
        for(; j<tmpNode.getNumChildren() - 1; ++j) {
          node_vec.push_back( tmpNode[j] );
        }
        tmpNode = tmpNode[j];
      }
    }
    if(!tmpNode.isConst()) {
      if(!preNode.isNull()) {
        if(preNode.getKind() == kind::CONST_STRING && !preNode.getConst<String>().isEmptyString() ) {
          node_vec.push_back( preNode );
        }
        preNode = Node::null();
      }
      node_vec.push_back( tmpNode );
    }else{
      if( preNode.isNull() ){
        preNode = tmpNode;
      }else{
        preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode.getConst<String>() ) );
      }
    }
  }
  if( !preNode.isNull() && ( preNode.getKind()!=kind::CONST_STRING || !preNode.getConst<String>().isEmptyString() ) ){
    node_vec.push_back( preNode );
  }
  retNode = mkConcat( kind::STRING_CONCAT, node_vec );
  Trace("strings-prerewrite") << "Strings::rewriteConcatString end " << retNode << std::endl;
  return retNode;
}


void TheoryStringsRewriter::mergeInto(std::vector<Node> &t, const std::vector<Node> &s) {
  for(std::vector<Node>::const_iterator itr=s.begin(); itr!=s.end(); itr++) {
    if(std::find(t.begin(), t.end(), (*itr)) == t.end()) {
      t.push_back( *itr );
    }
  }
}

void TheoryStringsRewriter::shrinkConVec(std::vector<Node> &vec) {
  unsigned i = 0;
  Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
  while(i < vec.size()) {
    if( vec[i] == emptysingleton ) {
      vec.erase(vec.begin() + i);
    } else if(vec[i].getKind()==kind::STRING_TO_REGEXP && i<vec.size()-1 && vec[i+1].getKind()==kind::STRING_TO_REGEXP) {
      Node tmp = NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, vec[i][0], vec[i+1][0]);
      tmp = rewriteConcatString(tmp);
      vec[i] = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, tmp);
      vec.erase(vec.begin() + i + 1);
    } else {
      i++;
    }
  }
}

Node TheoryStringsRewriter::applyAX( TNode node ) {
  Trace("regexp-ax") << "Regexp::AX start " << node << std::endl;
  Node retNode = node;

  int k = node.getKind();
  switch( k ) {
    case kind::REGEXP_UNION: {
      std::vector<Node> vec_nodes;
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_UNION) {
          for(unsigned j=0; j<tmp.getNumChildren(); j++) {
            if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp[j]) == vec_nodes.end()) {
              vec_nodes.push_back(tmp[j]);
            }
          }
        } else if(tmp.getKind() == kind::REGEXP_EMPTY) {
          // do nothing
        } else {
          if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp) == vec_nodes.end()) {
            vec_nodes.push_back(tmp);
          }
        }
      }
      if(vec_nodes.empty()) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else {
        retNode = vec_nodes.size() == 1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
      }
      break;
    }
    case kind::REGEXP_CONCAT: {
      std::vector< std::vector<Node> > vec_nodes;
      bool emptyflag = false;
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_EMPTY) {
          emptyflag = true;
          break;
        } else if(tmp == emptysingleton) {
          //do nothing
        } else if(vec_nodes.empty()) {
          if(tmp.getKind() == kind::REGEXP_UNION) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              std::vector<Node> vtmp;
              if(tmp[j].getKind() == kind::REGEXP_CONCAT) {
                for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                  vtmp.push_back(tmp[j][j2]);
                }
              } else {
                vtmp.push_back(tmp[j]);
              }
              vec_nodes.push_back(vtmp);
            }
          } else if(tmp.getKind() == kind::REGEXP_CONCAT) {
            std::vector<Node> vtmp;
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vtmp.push_back(tmp[j]);
            }
            vec_nodes.push_back(vtmp);
          } else {
            std::vector<Node> vtmp;
            vtmp.push_back(tmp);
            vec_nodes.push_back(vtmp);
          }
        } else {
          //non-empty vec
          if(tmp.getKind() == kind::REGEXP_UNION) {
            unsigned cnt = vec_nodes.size();
            for(unsigned i2=0; i2<cnt; i2++) {
              //std::vector<Node> vleft( vec_nodes[i2] );
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                if(tmp[j] == emptysingleton) {
                  vec_nodes.push_back( vec_nodes[i2] );
                } else {
                  std::vector<Node> vt( vec_nodes[i2] );
                  if(tmp[j].getKind() != kind::REGEXP_CONCAT) {
                    vt.push_back( tmp[j] );
                  } else {
                    for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                      vt.push_back(tmp[j][j2]);
                    }
                  }
                  vec_nodes.push_back(vt);
                }
              }
            }
            vec_nodes.erase(vec_nodes.begin(), vec_nodes.begin() + cnt);
          } else if(tmp.getKind() == kind::REGEXP_CONCAT) {
            for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                vec_nodes[i2].push_back(tmp[j]);
              }
            }
          } else {
            for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
              vec_nodes[i2].push_back(tmp);
            }
          }
        }
      }
      if(emptyflag) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else if(vec_nodes.empty()) {
        retNode = emptysingleton;
      } else if(vec_nodes.size() == 1) {
        shrinkConVec(vec_nodes[0]);
        retNode = vec_nodes[0].empty()? emptysingleton
          : vec_nodes[0].size()==1? vec_nodes[0][0]
          : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes[0]);
      } else {
        std::vector<Node> vtmp;
        for(unsigned i=0; i<vec_nodes.size(); i++) {
          shrinkConVec(vec_nodes[i]);
          if(!vec_nodes[i].empty()) {
            Node ntmp = vec_nodes[i].size()==1? vec_nodes[i][0]
              : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes[i]);
            vtmp.push_back(ntmp);
          }
        }
        retNode = vtmp.empty()? emptysingleton
          : vtmp.size()==1? vtmp[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vtmp);
      }
      break;
    }
    case kind::REGEXP_STAR: {
      Node tmp = applyAX(node[0]);
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      if(tmp.getKind() == kind::REGEXP_EMPTY || tmp == emptysingleton) {
        retNode = emptysingleton;
      } else {
        if(tmp.getKind() == kind::REGEXP_UNION) {
          std::vector<Node> vec;
          for(unsigned i=0; i<tmp.getNumChildren(); i++) {
            if(tmp[i] != emptysingleton) {
              vec.push_back(tmp[i]);
            }
          }
          if(vec.size() != tmp.getNumChildren()) {
            tmp = vec.size()==1? vec[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec) ;
          }
        } else if(tmp.getKind() == kind::REGEXP_STAR) {
          tmp = tmp[0];
        }
        if(tmp != node[0]) {
          retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, tmp );
        }
      }
      break;
    }
    case kind::REGEXP_INTER: {
      std::vector< std::vector<Node> > vec_nodes;
      bool emptyflag = false;
      bool epsflag = false;
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_EMPTY) {
          emptyflag = true;
          break;
        } else if(vec_nodes.empty()) {
          if(tmp.getKind() == kind::REGEXP_INTER) {
            std::vector<Node> vtmp;
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vtmp.push_back(tmp[j]);
            }
            vec_nodes.push_back(vtmp);
          } else if(tmp.getKind() == kind::REGEXP_UNION) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              std::vector<Node> vtmp;
              if(tmp[j].getKind() == kind::REGEXP_INTER) {
                for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                  vtmp.push_back(tmp[j][j2]);
                }
              } else {
                vtmp.push_back(tmp[j]);
              }
              vec_nodes.push_back(vtmp);
            }
          } else {
            if(tmp == emptysingleton) {
              epsflag = true;
            }
            std::vector<Node> vtmp;
            vtmp.push_back(tmp);
            vec_nodes.push_back(vtmp);
          }
        } else {
          //non-empty vec
          if(tmp.getKind() == kind::REGEXP_INTER) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
                if(std::find(vec_nodes[i2].begin(), vec_nodes[i2].end(), tmp[j]) == vec_nodes[i2].end()) {
                  vec_nodes[i2].push_back(tmp[j]);
                }
              }
            }
          } else if(tmp == emptysingleton) {
            if(!epsflag) {
              epsflag = true;
              for(unsigned j=0; j<vec_nodes.size(); j++) {
                vec_nodes[j].insert(vec_nodes[j].begin(), emptysingleton);
              }
            }
          } else if(tmp.getKind() == kind::REGEXP_UNION) {
            unsigned cnt = vec_nodes.size();
            for(unsigned i2=0; i2<cnt; i2++) {
              //std::vector<Node> vleft( vec_nodes[i2] );
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                std::vector<Node> vt(vec_nodes[i2]);
                if(tmp[j].getKind() != kind::REGEXP_INTER) {
                  if(std::find(vt.begin(), vt.end(), tmp[j]) == vt.end()) {
                    vt.push_back(tmp[j]);
                  }
                } else {
                  std::vector<Node> vtmp;
                  for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                    vtmp.push_back(tmp[j][j2]);
                  }
                  mergeInto(vt, vtmp);
                }
                vec_nodes.push_back(vt);
              }
            }
            vec_nodes.erase(vec_nodes.begin(), vec_nodes.begin() + cnt);
          } else {
            for(unsigned j=0; j<vec_nodes.size(); j++) {
              if(std::find(vec_nodes[j].begin(), vec_nodes[j].end(), tmp) == vec_nodes[j].end()) {
                vec_nodes[j].push_back(tmp);
              }
            }
          }
        }
      }
      if(emptyflag) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else if(vec_nodes.empty()) {
        //to check?
        retNode = emptysingleton;
      } else if(vec_nodes.size() == 1) {
        retNode = vec_nodes[0].empty() ? emptysingleton : vec_nodes[0].size() == 1 ? vec_nodes[0][0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes[0] );
      } else {
        std::vector<Node> vtmp;
        for(unsigned i=0; i<vec_nodes.size(); i++) {
          Node tmp = vec_nodes[i].empty()? emptysingleton : vec_nodes[i].size() == 1 ? vec_nodes[i][0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes[i] );
          vtmp.push_back(tmp);
        }
        retNode = vtmp.size() == 1? vtmp[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vtmp );
      }
      break;
    }
/*    case kind::REGEXP_UNION: {
      break;
    }*/
    case kind::REGEXP_SIGMA: {
      break;
    }
    case kind::REGEXP_EMPTY: {
      break;
    }
    //default: {
      //to check?
    //}
  }

  Trace("regexp-ax") << "Regexp::AX end " << node << " to\n               " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteConcatRegExp( TNode node ) {
  Assert( node.getKind() == kind::REGEXP_CONCAT );
  Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  bool emptyflag = false;
  for(unsigned int i=0; i<node.getNumChildren(); ++i) {
    Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp preNode: " << preNode << std::endl;
    Node tmpNode = node[i];
    if(tmpNode.getKind() == kind::REGEXP_CONCAT) {
      tmpNode = prerewriteConcatRegExp(node[i]);
      if(tmpNode.getKind() == kind::REGEXP_CONCAT) {
        unsigned j=0;
        if(!preNode.isNull()) {
          if(tmpNode[0].getKind() == kind::STRING_TO_REGEXP) {
            preNode = rewriteConcatString(
              NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, preNode, tmpNode[0][0] ) );
            node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
            preNode = Node::null();
          } else {
            node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
            preNode = Node::null();
            node_vec.push_back( tmpNode[0] );
          }
          ++j;
        }
        for(; j<tmpNode.getNumChildren() - 1; ++j) {
          node_vec.push_back( tmpNode[j] );
        }
        tmpNode = tmpNode[j];
      }
    }
    if( tmpNode.getKind() == kind::STRING_TO_REGEXP ) {
      if(preNode.isNull()) {
        preNode = tmpNode[0];
      } else {
        preNode = rewriteConcatString(
        NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, preNode, tmpNode[0] ) );
      }
    } else if( tmpNode.getKind() == kind::REGEXP_EMPTY ) {
      emptyflag = true;
      break;
    } else {
      if(!preNode.isNull()) {
        if(preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() ) {
          preNode = Node::null();
        } else {
          node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
          preNode = Node::null();
        }
      }
      node_vec.push_back( tmpNode );
    }
  }
  if(emptyflag) {
    std::vector< Node > nvec;
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
  } else {
    if(!preNode.isNull()) {
      bool bflag = (preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() );
      if(node_vec.empty() || !bflag ) {
        node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
      }
    }
    if(node_vec.size() > 1) {
      retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, node_vec);
    } else {
      retNode = node_vec[0];
    }
  }
  Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteOrRegExp(TNode node) {
  Assert( node.getKind() == kind::REGEXP_UNION );
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  bool allflag = false;
  for(unsigned i=0; i<node.getNumChildren(); ++i) {
    if(node[i].getKind() == kind::REGEXP_UNION) {
      Node tmpNode = prerewriteOrRegExp( node[i] );
      if(tmpNode.getKind() == kind::REGEXP_UNION) {
        for(unsigned int j=0; j<tmpNode.getNumChildren(); ++j) {
          if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
            if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
              node_vec.push_back( tmpNode[j] );
            }
          }
        }
      } else if(tmpNode.getKind() == kind::REGEXP_EMPTY) {
        //nothing
      } else if(tmpNode.getKind() == kind::REGEXP_STAR && tmpNode[0].getKind() == kind::REGEXP_SIGMA) {
        allflag = true;
        retNode = tmpNode;
        break;
      } else {
        if(std::find(node_vec.begin(), node_vec.end(), tmpNode) == node_vec.end()) {
          node_vec.push_back( tmpNode );
        }
      }
    } else if(node[i].getKind() == kind::REGEXP_EMPTY) {
      //nothing
    } else if(node[i].getKind() == kind::REGEXP_STAR && node[i][0].getKind() == kind::REGEXP_SIGMA) {
      allflag = true;
      retNode = node[i];
      break;
    } else {
      if(std::find(node_vec.begin(), node_vec.end(), node[i]) == node_vec.end()) {
        node_vec.push_back( node[i] );
      }
    }
  }
  if(!allflag) {
    std::vector< Node > nvec;
    retNode = node_vec.size() == 0 ? NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec ) :
          node_vec.size() == 1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, node_vec);
  }
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteAndRegExp(TNode node) {
  Assert( node.getKind() == kind::REGEXP_INTER );
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  //Node allNode = Node::null();
  for(unsigned i=0; i<node.getNumChildren(); ++i) {
    if(node[i].getKind() == kind::REGEXP_INTER) {
      Node tmpNode = prerewriteAndRegExp( node[i] );
      if(tmpNode.getKind() == kind::REGEXP_INTER) {
        for(unsigned int j=0; j<tmpNode.getNumChildren(); ++j) {
          if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
            node_vec.push_back( tmpNode[j] );
          }
        }
      } else if(tmpNode.getKind() == kind::REGEXP_EMPTY) {
        retNode = tmpNode;
        break;
      } else if(tmpNode.getKind() == kind::REGEXP_STAR && tmpNode[0].getKind() == kind::REGEXP_SIGMA) {
        //allNode = tmpNode;
      } else {
        if(std::find(node_vec.begin(), node_vec.end(), tmpNode) == node_vec.end()) {
          node_vec.push_back( tmpNode );
        }
      }
    } else if(node[i].getKind() == kind::REGEXP_EMPTY) {
      retNode = node[i];
      break;
    } else if(node[i].getKind() == kind::REGEXP_STAR && node[i][0].getKind() == kind::REGEXP_SIGMA) {
      //allNode = node[i];
    } else {
      if(std::find(node_vec.begin(), node_vec.end(), node[i]) == node_vec.end()) {
        node_vec.push_back( node[i] );
      }
    }
  }
  if( retNode==node ){
    std::vector< Node > nvec;
    retNode = node_vec.size() == 0 ?
          NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, NodeManager::currentNM()->mkNode(kind::REGEXP_SIGMA, nvec)) :
          node_vec.size() == 1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_INTER, node_vec);
  }
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp end " << retNode << std::endl;
  return retNode;
}

bool TheoryStringsRewriter::isConstRegExp( TNode t ) {
  if( t.getKind()==kind::STRING_TO_REGEXP ) {
    return t[0].isConst();
  }else{
    for( unsigned i = 0; i<t.getNumChildren(); ++i ) {
      if( !isConstRegExp(t[i]) ){
        return false;
      }
    }
    return true;
  }
}

bool TheoryStringsRewriter::testConstStringInRegExp( CVC4::String &s, unsigned int index_start, TNode r ) {
  Assert( index_start <= s.size() );
  Trace("regexp-debug") << "Checking " << s << " in " << r << ", starting at " << index_start << std::endl;
  int k = r.getKind();
  switch( k ) {
    case kind::STRING_TO_REGEXP: {
      CVC4::String s2 = s.substr( index_start, s.size() - index_start );
      if(r[0].getKind() == kind::CONST_STRING) {
        return ( s2 == r[0].getConst<String>() );
      } else {
        Assert( false, "RegExp contains variables" );
        return false;
      }
    }
    case kind::REGEXP_CONCAT: {
      if( s.size() != index_start ) {
        std::vector<int> vec_k( r.getNumChildren(), -1 );
        int start = 0;
        int left = (int) s.size() - index_start;
        int i=0;
        while( i<(int) r.getNumChildren() ) {
          bool flag = true;
          if( i == (int) r.getNumChildren() - 1 ) {
            if( testConstStringInRegExp( s, index_start + start, r[i] ) ) {
              return true;
            }
          } else if( i == -1 ) {
            return false;
          } else {
            for(vec_k[i] = vec_k[i] + 1; vec_k[i] <= left; ++vec_k[i]) {
              CVC4::String t = s.substr(index_start + start, vec_k[i]);
              if( testConstStringInRegExp( t, 0, r[i] ) ) {
                start += vec_k[i]; left -= vec_k[i]; flag = false;
                ++i; vec_k[i] = -1;
                break;
              }
            }
          }

          if(flag) {
            --i;
            if(i >= 0) {
              start -= vec_k[i]; left += vec_k[i];
            }
          }
        }
        return false;
      } else {
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
        }
        return true;
      }
    }
    case kind::REGEXP_UNION: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(testConstStringInRegExp( s, index_start, r[i] )) return true;
      }
      return false;
    }
    case kind::REGEXP_INTER: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
      }
      return true;
    }
    case kind::REGEXP_STAR: {
      if( s.size() != index_start ) {
        for(unsigned k=s.size() - index_start; k>0; --k) {
          CVC4::String t = s.substr(index_start, k);
          if( testConstStringInRegExp( t, 0, r[0] ) ) {
            if( index_start + k == s.size() || testConstStringInRegExp( s, index_start + k, r ) ) {
              return true;
            }
          }
        }
        return false;
      } else {
        return true;
      }
    }
    case kind::REGEXP_EMPTY: {
      return false;
    }
    case kind::REGEXP_SIGMA: {
      if(s.size() == index_start + 1) {
        return true;
      } else {
        return false;
      }
    }
    case kind::REGEXP_RANGE: {
      if(s.size() == index_start + 1) {
        unsigned char a = r[0].getConst<String>().getFirstChar();
        unsigned char b = r[1].getConst<String>().getFirstChar();
        unsigned char c = s.getLastChar();
        return (a <= c && c <= b);
      } else {
        return false;
      }
    }
    case kind::REGEXP_LOOP: {
      unsigned l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if(s.size() == index_start) {
        return l==0? true : testConstStringInRegExp(s, index_start, r[0]);
      } else if(l==0 && r[1]==r[2]) {
        return false;
      } else {
        Assert(r.getNumChildren() == 3, "String rewriter error: LOOP has 2 children");
        if(l==0) {
          //R{0,u}
          unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          for(unsigned len=s.size() - index_start; len>=1; len--) {
            CVC4::String t = s.substr(index_start, len);
            if(testConstStringInRegExp(t, 0, r[0])) {
              if(len + index_start == s.size()) {
                return true;
              } else {
                Node num2 = NodeManager::currentNM()->mkConst( CVC4::Rational(u - 1) );
                Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], r[1], num2);
                if(testConstStringInRegExp(s, index_start+len, r2)) {
                  return true;
                }
              }
            }
          }
          return false;
        } else {
          //R{l,l}
          Assert(r[1]==r[2], "String rewriter error: LOOP nums are not equal");
          if(l>s.size() - index_start) {
            if(testConstStringInRegExp(s, s.size(), r[0])) {
              l = s.size() - index_start;
            } else {
              return false;
            }
          }
          for(unsigned len=1; len<=s.size() - index_start; len++) {
            CVC4::String t = s.substr(index_start, len);
            if(testConstStringInRegExp(t, 0, r[0])) {
              Node num2 = NodeManager::currentNM()->mkConst( CVC4::Rational(l - 1) );
              Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], num2, num2);
              if(testConstStringInRegExp(s, index_start+len, r2)) {
                return true;
              }
            }
          }
          return false;
        }
      }
    }
    default: {
      Trace("strings-error") << "Unsupported term: " << r << " in testConstStringInRegExp." << std::endl;
      Unreachable();
      return false;
    }
  }
}

Node TheoryStringsRewriter::rewriteMembership(TNode node) {
  Node retNode = node;
  Node x = node[0];
  Node r = node[1];//applyAX(node[1]);

  if(node[0].getKind() == kind::STRING_CONCAT) {
    x = rewriteConcatString(node[0]);
  }

  if(r.getKind() == kind::REGEXP_EMPTY) {
    retNode = NodeManager::currentNM()->mkConst( false );
  } else if(x.getKind()==kind::CONST_STRING && isConstRegExp(r)) {
    //test whether x in node[1]
    CVC4::String s = x.getConst<String>();
    retNode = NodeManager::currentNM()->mkConst( testConstStringInRegExp( s, 0, r ) );
  } else if(r.getKind() == kind::REGEXP_SIGMA) {
    Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
    retNode = one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x));
  } else if( r.getKind() == kind::REGEXP_STAR ) {
    if( r[0].getKind() == kind::REGEXP_SIGMA ){
      retNode = NodeManager::currentNM()->mkConst( true );
    }
  }else if( r.getKind() == kind::REGEXP_CONCAT ){
    bool allSigma = true;
    bool allString = true;
    std::vector< Node > cc;
    for(unsigned i=0; i<r.getNumChildren(); i++) {
      Assert( r[i].getKind() != kind::REGEXP_EMPTY );
      if( r[i].getKind() != kind::REGEXP_SIGMA ){
        allSigma = false;
      }
      if( r[i].getKind() != kind::STRING_TO_REGEXP ){
        allString = false;
      }else{
        cc.push_back( r[i] );
      }
    }
    if( allSigma ){
      Node num = NodeManager::currentNM()->mkConst( ::CVC4::Rational( r.getNumChildren() ) );
      retNode = num.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x));
    }else if( allString ){
      retNode = x.eqNode( mkConcat( kind::STRING_CONCAT, cc ) );
    }
  }else if( r.getKind()==kind::REGEXP_INTER || r.getKind()==kind::REGEXP_UNION ){
    std::vector< Node > mvec;
    for( unsigned i=0; i<r.getNumChildren(); i++ ){
      mvec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r[i] ) );
    }
    retNode = NodeManager::currentNM()->mkNode( r.getKind()==kind::REGEXP_INTER ? kind::AND : kind::OR, mvec );
  }else if(r.getKind() == kind::STRING_TO_REGEXP) {
    retNode = x.eqNode(r[0]);
  }else if(x != node[0] || r != node[1]) {
    retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r );
  }

  //do simple consumes
  if( retNode==node ){
    if( r.getKind()==kind::REGEXP_STAR ){
      for( unsigned dir=0; dir<=1; dir++ ){
        std::vector< Node > mchildren;
        getConcat( x, mchildren );
        bool success = true;
        while( success ){
          success = false;
          std::vector< Node > children;
          getConcat( r[0], children );
          Node scn = simpleRegexpConsume( mchildren, children, dir );
          if( !scn.isNull() ){
            Trace("regexp-ext-rewrite") << "Regexp star : const conflict : " << node << std::endl;
            return scn;
          }else if( children.empty() ){
            //fully consumed one copy of the STAR
            if( mchildren.empty() ){
              Trace("regexp-ext-rewrite") << "Regexp star : full consume : " << node << std::endl;
              return NodeManager::currentNM()->mkConst( true );
            }else{
              retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, mkConcat( kind::STRING_CONCAT, mchildren ), r );
              success = true;
            }
          }
        }
        if( retNode!=node ){
          Trace("regexp-ext-rewrite") << "Regexp star : rewrite " << node << " -> " << retNode << std::endl;
          break;
        }
      }
    }else{
      std::vector< Node > children;
      getConcat( r, children );
      std::vector< Node > mchildren;
      getConcat( x, mchildren );
      unsigned prevSize = children.size() + mchildren.size();
      Node scn = simpleRegexpConsume( mchildren, children );
      if( !scn.isNull() ){
        Trace("regexp-ext-rewrite") << "Regexp : const conflict : " << node << std::endl;
        return scn;
      }else{
        if( (children.size() + mchildren.size())!=prevSize ){
          if( children.empty() ){
            retNode = NodeManager::currentNM()->mkConst( mchildren.empty() );
          }else{
            retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, mkConcat( kind::STRING_CONCAT, mchildren ), mkConcat( kind::REGEXP_CONCAT, children ) );
          }
          Trace("regexp-ext-rewrite") << "Regexp : rewrite : " << node << " -> " << retNode << std::endl;
        }
      }
    }
  }
  return retNode;
}

RewriteResponse TheoryStringsRewriter::postRewrite(TNode node) {
  Trace("strings-postrewrite") << "Strings::postRewrite start " << node << std::endl;
  Node retNode = node;
  Node orig = retNode;

  if(node.getKind() == kind::EQUAL) {
    Node leftNode  = node[0];
    if(node[0].getKind() == kind::STRING_CONCAT) {
      leftNode = rewriteConcatString(node[0]);
    }
    Node rightNode = node[1];
    if(node[1].getKind() == kind::STRING_CONCAT) {
      rightNode = rewriteConcatString(node[1]);
    }

    if(leftNode == rightNode) {
      retNode = NodeManager::currentNM()->mkConst(true);
    } else if(leftNode.isConst() && rightNode.isConst()) {
      retNode = NodeManager::currentNM()->mkConst(false);
    } else if(leftNode > rightNode) {
      retNode = NodeManager::currentNM()->mkNode(kind::EQUAL, rightNode, leftNode);
    } else if( leftNode != node[0] || rightNode != node[1]) {
      retNode = NodeManager::currentNM()->mkNode(kind::EQUAL, leftNode, rightNode);
    }
    return RewriteResponse( orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode );
  } else if(node.getKind() == kind::STRING_LENGTH) {
    if( node[0].isConst() ){
      retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( node[0].getConst<String>().size() ) );
    }else if( node[0].getKind() == kind::STRING_CONCAT ){
      std::vector<Node> node_vec;
      for(unsigned int i=0; i<node[0].getNumChildren(); ++i) {
        if( node[0][i].isConst() ){
          node_vec.push_back( NodeManager::currentNM()->mkConst( ::CVC4::Rational( node[0][i].getConst<String>().size() ) ) );
        } else {
          node_vec.push_back( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0][i]) );
        }
      }
      retNode = NodeManager::currentNM()->mkNode(kind::PLUS, node_vec);
    }else if( node[0].getKind()==kind::STRING_STRREPL ){
      if( node[0][1].isConst() && node[0][2].isConst() ){
        if( node[0][1].getConst<String>().size()==node[0][2].getConst<String>().size() ){
          retNode = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, node[0][0] );
        }
      }else{
        //TODO : improve (length entailed equal)
        
      }
    }
  }else if( node.getKind() == kind::STRING_CONCAT ){
    retNode = rewriteConcatString(node);
  }else if( node.getKind() == kind::STRING_SUBSTR ){
    retNode = rewriteSubstr( node );
  }else if( node.getKind() == kind::STRING_STRCTN ){
    retNode = rewriteContains( node );
  }else if( node.getKind()==kind::STRING_STRIDOF ){
    retNode = rewriteIndexof( node );
  }else if( node.getKind() == kind::STRING_STRREPL ){
    retNode = rewriteReplace( node );
  }else if( node.getKind() == kind::STRING_IN_REGEXP ){
    retNode = rewriteMembership(node);
  }else if( node.getKind() == kind::STRING_CHARAT ){
    Node one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
    retNode = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, node[0], node[1], one);
  }else if( node.getKind() == kind::STRING_PREFIX ){
    if( node[0].isConst() && node[1].isConst() ){
      CVC4::String s = node[1].getConst<String>();
      CVC4::String t = node[0].getConst<String>();
      retNode = NodeManager::currentNM()->mkConst( false );
      if(s.size() >= t.size()) {
        if(t == s.substr(0, t.size())) {
          retNode = NodeManager::currentNM()->mkConst( true );
        }
      }
    } else {
      Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
      Node lent = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
      retNode = NodeManager::currentNM()->mkNode(kind::AND,
            NodeManager::currentNM()->mkNode(kind::GEQ, lent, lens),
            node[0].eqNode(NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, node[1],
                    NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) ), lens)));
    }
  }else if( node.getKind() == kind::STRING_SUFFIX ){
    if(node[0].isConst() && node[1].isConst()) {
      CVC4::String s = node[1].getConst<String>();
      CVC4::String t = node[0].getConst<String>();
      retNode = NodeManager::currentNM()->mkConst( false );
      if(s.size() >= t.size()) {
        if(t == s.substr(s.size() - t.size(), t.size())) {
          retNode = NodeManager::currentNM()->mkConst( true );
        }
      }
    } else {
      Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
      Node lent = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
      retNode = NodeManager::currentNM()->mkNode(kind::AND,
            NodeManager::currentNM()->mkNode(kind::GEQ, lent, lens),
            node[0].eqNode(NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, node[1],
                    NodeManager::currentNM()->mkNode(kind::MINUS, lent, lens), lens)));
    }
  }else if(node.getKind() == kind::STRING_ITOS || node.getKind() == kind::STRING_U16TOS || node.getKind() == kind::STRING_U32TOS) {
    if(node[0].isConst()) {
      bool flag = false;
      std::string stmp = node[0].getConst<Rational>().getNumerator().toString();
      if(node.getKind() == kind::STRING_U16TOS) {
        CVC4::Rational r1(UINT16_MAX);
        CVC4::Rational r2 = node[0].getConst<Rational>();
        if(r2>r1) {
          flag = true;
        }
      } else if(node.getKind() == kind::STRING_U32TOS) {
        CVC4::Rational r1(UINT32_MAX);
        CVC4::Rational r2 = node[0].getConst<Rational>();
        if(r2>r1) {
          flag = true;
        }
      }
      //std::string stmp = static_cast<std::ostringstream*>( &(std::ostringstream() << node[0]) )->str();
      if(flag || stmp[0] == '-') {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
      } else {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String(stmp) );
      }
    }
  }else if(node.getKind() == kind::STRING_STOI || node.getKind() == kind::STRING_STOU16 || node.getKind() == kind::STRING_STOU32) {
    if(node[0].isConst()) {
      CVC4::String s = node[0].getConst<String>();
      if(s.isNumber()) {
        std::string stmp = s.toString();
        //if(stmp[0] == '0' && stmp.size() != 1) {
          //TODO: leading zeros
          //retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
        //} else {
          bool flag = false;
          CVC4::Rational r2(stmp.c_str());
          if(node.getKind() == kind::STRING_U16TOS) {
            CVC4::Rational r1(UINT16_MAX);
            if(r2>r1) {
              flag = true;
            }
          } else if(node.getKind() == kind::STRING_U32TOS) {
            CVC4::Rational r1(UINT32_MAX);
            if(r2>r1) {
              flag = true;
            }
          }
          if(flag) {
            retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
          } else {
            retNode = NodeManager::currentNM()->mkConst( r2 );
          }
        //}
      } else {
        retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
      }
    } else if(node[0].getKind() == kind::STRING_CONCAT) {
      for(unsigned i=0; i<node[0].getNumChildren(); ++i) {
        if(node[0][i].isConst()) {
          CVC4::String t = node[0][i].getConst<String>();
          if(!t.isNumber()) {
            retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
            break;
          }
        }
      }
    }
  }

  Trace("strings-postrewrite") << "Strings::postRewrite returning " << retNode << std::endl;
  if( orig!=retNode ){
    Trace("strings-rewrite") << "Strings: post-rewrite " << orig << " to " << retNode << std::endl;
    return RewriteResponse(REWRITE_AGAIN_FULL, retNode);
  }else{
    return RewriteResponse(REWRITE_DONE, retNode);
  }
}

bool TheoryStringsRewriter::hasEpsilonNode(TNode node) {
  for(unsigned int i=0; i<node.getNumChildren(); i++) {
    if(node[i].getKind() == kind::STRING_TO_REGEXP && node[i][0].getKind() == kind::CONST_STRING && node[i][0].getConst<String>().isEmptyString()) {
      return true;
    }
  }
  return false;
}


void TheoryStringsRewriter::getLengthEntail( Node s, Node& lower, Node& upper ) {
  Assert( s.getType().isString() );
  if( s.getKind() == kind::STRING_CONCAT ){
    //can abstract order dependent here
    std::vector< Node > ll;
    std::vector< Node > uu;
    for( unsigned i=0; i<s.getNumChildren(); i++ ){
      Node l;
      Node u;
      getLengthEntail( s[i], l, u );
      ll.push_back( l );
      uu.push_back( u );
    }
    lower = NodeManager::currentNM()->mkNode( kind::PLUS, ll );
    upper = NodeManager::currentNM()->mkNode( kind::PLUS, uu );
  }else if( s.getKind()==kind::STRING_SUBSTR ){
    if( s[2].isConst() ){
      Assert( s[2].getConst<Rational>().sgn()==1 );
      upper = s[2];
    }
  }
  if( lower.isNull() ){
    lower = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, getApproximation( s, true ) );
  }
  if( upper.isNull() ){
    upper = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, getApproximation( s, false ) );
  }
}

bool TheoryStringsRewriter::entailCheck( Node ieq ) {
  ieq = Rewriter::rewrite( ieq );
  if( ieq==NodeManager::currentNM()->mkConst(true) ){
    return true;
  }else if( ieq.getKind()==kind::GEQ ){
    //can drop positive length factors
    Node lhs_lb = getApproximation( ieq[0], true );
    Node lb_cmp = NodeManager::currentNM()->mkNode( kind::GEQ, lhs_lb, ieq[1] );
    lb_cmp = Rewriter::rewrite( lb_cmp );
    if( lb_cmp==NodeManager::currentNM()->mkConst(true) ){
      return true;
    }
  }
  return false;
}

// if isLower=true 
//    if n is a string, then return n' where n' is a substring of n
//    if n is an int, then return n' where n' <= n
// if isLower=false 
//    if n is a string, then return n' where n is a substring of n'
//    if n is an int, then return n' where n <= n'
Node TheoryStringsRewriter::getApproximation( Node n, bool isLower, bool ensurePrefix, bool ensureSuffix ) {
  if( !n.isConst() ){
    if( n.getType().isString() ){
      //TODO : improve
      if( ensurePrefix || ensureSuffix ){
        return n;
      }
      if( n.getKind()==kind::STRING_CONCAT ){
        //simplify substr from the endpoints?
        std::vector< Node > cc;
        bool childChanged = false;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = getApproximation( n[i], isLower, i>0 || ensurePrefix, (i+1)<n.getNumChildren() || ensureSuffix );
          childChanged = childChanged || nc!=n[i];
          cc.push_back( nc );
        }
        if( childChanged ){
          return NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, cc );
        }
      }else if( n.getKind() == kind::STRING_SUBSTR ){
        if( isLower ){
          //tighten : find things that must be in  TODO
          Node upper1 = getApproximation( n[1], false );
          Node lower2 = getApproximation( n[2], true );
          
        
          return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
        }else{
          //tighten : find things that must be out  TODO
          Node lower1 = getApproximation( n[1], true );
          Node upper2 = getApproximation( n[2], false );


          return getApproximation( n[0], isLower, ensurePrefix, ensureSuffix );
        }
      }
    }
    if( n.getType().isReal() ){
      if( n.getKind()==kind::MULT ){
        if( n.getNumChildren()==2 && n[0].isConst() ){
          if( n[0].getConst<Rational>().sgn()==1 ){
            return NodeManager::currentNM()->mkNode( kind::MULT, n[0], getApproximation( n[1], isLower ) );
          }else{
            Assert( n[0].getConst<Rational>().sgn()==-1 );
            return NodeManager::currentNM()->mkNode( kind::MULT, n[0], getApproximation( n[1], !isLower ) );
          }
        }
      }else if( n.getKind()==kind::STRING_STRIDOF ){
        if( isLower ){
          //tighten : if definite contains, then it must be at least 0
          Node cnt_check = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, n[0], n[1] );
          cnt_check = Rewriter::rewrite( cnt_check );
          if( cnt_check==NodeManager::currentNM()->mkConst(true) ){
            return NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
          }else{
            return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
          }
        }else{
          Node upper0 = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, getApproximation( n[0], false ) );
          Node lower1 = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, getApproximation( n[1], true ) );
          Node ret = NodeManager::currentNM()->mkNode( kind::MINUS, upper0, lower1 );
          Node ieq = NodeManager::currentNM()->mkNode( kind::GEQ, ret, NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) ) );
          if( entailCheck( ieq ) ){
            return ret;
          }else{
            return upper0;
          }
        }
      }else if( n.getKind()==kind::STRING_LENGTH ){
        if( isLower ){
          return NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
        }else{
          return n;
        }
      }else if( n.getKind()==kind::PLUS ){
        std::vector< Node > sum;
        bool childChanged = false;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = getApproximation( n[i], isLower );
          childChanged = childChanged || nc!=n[i];
          sum.push_back( nc );
        }
        if( childChanged ){
          return NodeManager::currentNM()->mkNode( kind::PLUS, sum );
        }
      }
    }
  }
  return n;
}


RewriteResponse TheoryStringsRewriter::preRewrite(TNode node) {
  Node retNode = node;
  Node orig = retNode;
  Trace("strings-prerewrite") << "Strings::preRewrite start " << node << std::endl;

  if(node.getKind() == kind::STRING_CONCAT) {
    retNode = rewriteConcatString(node);
  }else if(node.getKind() == kind::REGEXP_CONCAT) {
    retNode = prerewriteConcatRegExp(node);
  } else if(node.getKind() == kind::REGEXP_UNION) {
    retNode = prerewriteOrRegExp(node);
  } else if(node.getKind() == kind::REGEXP_INTER) {
    retNode = prerewriteAndRegExp(node);
  }
  else if(node.getKind() == kind::REGEXP_STAR) {
    if(node[0].getKind() == kind::REGEXP_STAR) {
      retNode = node[0];
    } else if(node[0].getKind() == kind::STRING_TO_REGEXP && node[0][0].getKind() == kind::CONST_STRING && node[0][0].getConst<String>().isEmptyString()) {
      retNode = node[0];
    } else if(node[0].getKind() == kind::REGEXP_EMPTY) {
      retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
    } else if(node[0].getKind() == kind::REGEXP_UNION) {
      Node tmpNode = prerewriteOrRegExp(node[0]);
      if(tmpNode.getKind() == kind::REGEXP_UNION) {
        if(hasEpsilonNode(node[0])) {
          std::vector< Node > node_vec;
          for(unsigned int i=0; i<node[0].getNumChildren(); i++) {
            if(node[0][i].getKind() == kind::STRING_TO_REGEXP && node[0][i][0].getKind() == kind::CONST_STRING && node[0][i][0].getConst<String>().isEmptyString()) {
              //return true;
            } else {
              node_vec.push_back(node[0][i]);
            }
          }
          retNode = node_vec.size()==1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, node_vec);
          retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, retNode);
        }
      } else if(tmpNode.getKind() == kind::STRING_TO_REGEXP && tmpNode[0].getKind() == kind::CONST_STRING && tmpNode[0].getConst<String>().isEmptyString()) {
        retNode = tmpNode;
      } else {
        retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, tmpNode);
      }
    }
  } else if(node.getKind() == kind::REGEXP_PLUS) {
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, node[0], NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, node[0]));
  } else if(node.getKind() == kind::REGEXP_OPT) {
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION,
          NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) ),
          node[0]);
  } else if(node.getKind() == kind::REGEXP_RANGE) {
    if(node[0] == node[1]) {
      retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, node[0] );
    }
    /*std::vector< Node > vec_nodes;
    unsigned char c = node[0].getConst<String>().getFirstChar();
    unsigned char end = node[1].getConst<String>().getFirstChar();
    for(; c<=end; ++c) {
      Node n = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String( c ) ) );
      vec_nodes.push_back( n );
    }
    if(vec_nodes.size() == 1) {
      retNode = vec_nodes[0];
    } else {
      retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
    }*/
  } else if(node.getKind() == kind::REGEXP_LOOP) {
    Node r = node[0];
    if(r.getKind() == kind::REGEXP_STAR) {
      retNode = r;
    } else {
      /* //lazy
      Node n1 = Rewriter::rewrite( node[1] );
      if(!n1.isConst()) {
        throw LogicException("re.loop contains non-constant integer (1).");
      }
      CVC4::Rational rz(0);
      CVC4::Rational RMAXINT(LONG_MAX);
      AlwaysAssert(rz <= n1.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (1)");
      Assert(n1.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (1)");
      unsigned l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
      if(node.getNumChildren() == 3) {
        Node n2 = Rewriter::rewrite( node[2] );
        if(!n2.isConst()) {
          throw LogicException("re.loop contains non-constant integer (2).");
        }
        if(n1 == n2) {
          if(l == 0) {
            retNode = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP,
              NodeManager::currentNM()->mkConst(CVC4::String("")));
          } else if(l == 1) {
            retNode = node[0];
          }
        } else {
          AlwaysAssert(rz <= n2.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (2)");
          Assert(n2.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (2)");
          unsigned u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
          AlwaysAssert(l <= u, "REGEXP_LOOP (1) > REGEXP_LOOP (2)");
          if(l != 0) {
            Node zero = NodeManager::currentNM()->mkConst( CVC4::Rational(0) );
            Node num = NodeManager::currentNM()->mkConst( CVC4::Rational(u - l) );
            Node t1 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], n1, n1);
            Node t2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], zero, num);
            retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, t1, t2);
          }
        }
      } else {
        retNode = l==0? NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, node[0]) :
          NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
            NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], n1, n1),
            NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, node[0]));
      }
    }*/ //lazy
    /*else {*/
      // eager
      TNode n1 = Rewriter::rewrite( node[1] );
      //
      if(!n1.isConst()) {
        throw LogicException("re.loop contains non-constant integer (1).");
      }
      AlwaysAssert(n1.getConst<Rational>().sgn()>=0, "Negative integer in string REGEXP_LOOP (1)");
      Assert(n1.getConst<Rational>() <= Rational(LONG_MAX), "Exceeded LONG_MAX in string REGEXP_LOOP (1)");
      //
      unsigned l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<l; i++) {
        vec_nodes.push_back(r);
      }
      if(node.getNumChildren() == 3) {
        TNode n2 = Rewriter::rewrite( node[2] );
        //if(!n2.isConst()) {
        //  throw LogicException("re.loop contains non-constant integer (2).");
        //}
        Node n = vec_nodes.size()==0 ? NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(CVC4::String("")))
          : vec_nodes.size()==1 ? r : prerewriteConcatRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes));
        //Assert(n2.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (2)");
        unsigned u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
        if(u <= l) {
          retNode = n;
        } else {
          std::vector< Node > vec2;
          vec2.push_back(n);
          for(unsigned j=l; j<u; j++) {
            vec_nodes.push_back(r);
            n = vec_nodes.size()==1? r : prerewriteConcatRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes));
            vec2.push_back(n);
          }
          retNode = prerewriteOrRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec2));
        }
      } else {
        Node rest = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, r);
        retNode = vec_nodes.size()==0? rest : prerewriteConcatRegExp( vec_nodes.size()==1?
                 NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, r, rest)
                :NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
                  NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes), rest) );
      }
    }
    Trace("strings-lp") << "Strings::lp " << node << " => " << retNode << std::endl;
  }

  Trace("strings-prerewrite") << "Strings::preRewrite returning " << retNode << std::endl;
  if( orig!=retNode ){
    Trace("strings-rewrite") << "Strings: pre-rewrite " << orig << " to " << retNode << std::endl;
    return RewriteResponse(REWRITE_AGAIN_FULL, retNode);
  }else{
    return RewriteResponse(REWRITE_DONE, retNode);
  }
}


Node TheoryStringsRewriter::rewriteSubstr( Node node ) {
  Node zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
  if( node[0].isConst() ){
    if( node[0].getConst<String>().size()==0 ){
      return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    }
  }
  if( node[2].isConst() ) {
    if( node[2].getConst<Rational>().sgn()<=0 ){
      return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    }
  }
  std::vector< Node > children;
  if( node[1].isConst() ){
    CVC4::Rational RMAXINT(LONG_MAX);
    if( node[1].getConst<Rational>()>RMAXINT ){
      Assert(node[1].getConst<Rational>() <= RMAXINT, "Number exceeds LONG_MAX in string substr");
      return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    }else if( node[1].getConst<Rational>().sgn()<0 ){
      return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    }else{
      getConcat( node[0], children );
      Node start = node[1];
      if( stripConstantPrefix( children, start ) ){
        return NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, mkConcat( kind::STRING_CONCAT, children ), start, node[2] );
      }else{
        if( node[2].isConst() ){
          if( children[0].isConst() ){
            Assert( node[1].getConst<Rational>().sgn()==0 );
            Assert( node[2].getConst<Rational>().sgn()>=0);
            CVC4::Rational v2( node[2].getConst<Rational>() );
            CVC4::Rational size(children[0].getConst<String>().size());
            if( v2<=size ){
              //since size is smaller than MAX_INT, v2 is smaller than MAX_INT
              Assert(v2 <= RMAXINT, "Number exceeds LONG_MAX in string substr v2");
              size_t j = v2.getNumerator().toUnsignedInt();
              return NodeManager::currentNM()->mkConst( children[0].getConst<String>().substr(0, j) );
            }else{
              //pull first argument
              Node cfirst = children[0];
              children.erase( children.begin(), children.begin() + 1 );
              size_t rm = v2.getNumerator().toUnsignedInt() - size.getNumerator().toUnsignedInt();
              return NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, cfirst,
                                                       NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, mkConcat( kind::STRING_CONCAT, children ), node[1],
                                                                                         NodeManager::currentNM()->mkConst( ::CVC4::Rational( rm ) ) ) );
            }
          }
        }else{
          if( node[1]==zero && node[2].getKind()==kind::STRING_LENGTH && node[2][0]==node[0] ){
            return node[0];
          }
        }
      }
    }
  }else{
    getConcat( node[0], children );
  }

  //combine substr
  if( node[0].getKind()==kind::STRING_SUBSTR ){
    Node cmp_ss = NodeManager::currentNM()->mkNode( kind::LEQ, NodeManager::currentNM()->mkNode( kind::PLUS, node[1], node[2] ), node[0][2] );
    if( entailCheck( cmp_ss ) ){
      Node ret = NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, node[0][0], NodeManager::currentNM()->mkNode( kind::PLUS, node[0][1], node[1] ), node[2] );;
      Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " by combine substr." << std::endl;
      return ret;
    }
  }

  //length entailment
  Node l, u;
  getLengthEntail( node[0], l, u );
  Node snode = node[1];
  while( snode.getKind()==kind::STRING_STRIDOF ){
    snode = snode[2];
  }
  //check if ( node[1] = -1   OR  node[1] >= snode >= u >= len( node[0] ) )
  Node cmp_su = NodeManager::currentNM()->mkNode( kind::GEQ, snode, u );
  if( entailCheck( cmp_su ) ){
    //always out of scope
    Trace("strings-rewrite-advanced") << "Rewrite " << node << " to empty string by start position to length entailment." << std::endl;
    return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
  }
/*
  if( node[1]==zero ){
    Node cmp_u = NodeManager::currentNM()->mkNode( kind::GEQ, node[2], u );
    if( entailCheck( cmp_u ) ){
      Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << node[0] << " by coverage entailment." << std::endl;
      //always covers entire string
      return node[0];
    }
  }
*/
  //symbolic length analysis
  for( unsigned r=0; r<2; r++ ){
    if( ( r==0 && node[1]!=zero ) || ( r==1 && node[1]==zero ) ){
      Node curr_s = r==0 ? node[1] : node[2];
      //check entailed empty by comparison with zero
      Node cmp_emp = NodeManager::currentNM()->mkNode( r==0 ? kind::LT : kind::LEQ, curr_s, zero );
      if( entailCheck( cmp_emp ) ){
        Trace("strings-rewrite-advanced") << "Rewrite " << node << " to empty string by zero entailment, r=" << r << "." << std::endl;
        return NodeManager::currentNM()->mkConst( ::CVC4::String("") );
      }
      //strip off components while quantity is entailed positive
      std::vector< Node > childrenr;
      unsigned sindex = stripSymbolicLength( children, childrenr, curr_s );
      if( sindex>0 ){
        if( r==0 ){
          Node ret = NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, mkConcat( kind::STRING_CONCAT, children ), curr_s, node[2] );
          Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " by substr symbolic start position analysis." << std::endl;
          return ret;
        }else{
          if( curr_s!=zero ){
            childrenr.push_back( NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, mkConcat( kind::STRING_CONCAT, children ), node[1], curr_s ) );
          }
          Node ret = mkConcat( kind::STRING_CONCAT, childrenr );
          Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " by substr symbolic length analysis." << std::endl;
          return ret;
        }
      }
    }
  }

  //normalize the last argument
  Node max_end = NodeManager::currentNM()->mkNode( kind::MINUS, NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, node[0] ), node[1] );
  Node cmp_e = NodeManager::currentNM()->mkNode( kind::GT, node[2], max_end );
  if( entailCheck( cmp_e ) ){
    Node ret = NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, node[0], node[1], max_end );
    Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " by redundant covering." << std::endl;
    //covers entire string, and max_end suffices
    return ret;
  }

  return node;
}

Node TheoryStringsRewriter::rewriteContains( Node node ) {
  if( node[0]==node[1] ){
    return NodeManager::currentNM()->mkConst( true );
  }else if( node[0].isConst() ){
    if( node[1].isConst() ){
      CVC4::String s = node[0].getConst<String>();
      CVC4::String t = node[1].getConst<String>();
      return NodeManager::currentNM()->mkConst( s.find(t)!=std::string::npos );
    }else{
      if( node[0].getConst<String>().size()==0 ){
        return NodeManager::currentNM()->mkNode( kind::EQUAL, node[0], node[1] );
      }else if( node[1].getKind()==kind::STRING_CONCAT ){
        int firstc, lastc;
        if( !canConstantContainConcat( node[0], node[1], firstc, lastc ) ){
          return NodeManager::currentNM()->mkConst( false );
        }
      }
    }
  }else if( node[0].getKind()==kind::STRING_CONCAT ){
    std::vector< Node > nc1;
    getConcat( node[0], nc1 );
    std::vector< Node > nc2;
    getConcat( node[1], nc2 );
    std::vector< Node > nr;
    //component-wise containment
    if( componentContains( nc1, nc2, nr )!=-1 ){
      return NodeManager::currentNM()->mkConst( true );
    }
    
    //strip endpoints
    std::vector< Node > nb;
    std::vector< Node > ne;
    if( stripConstantEndpoints( nc1, nc2, nb, ne ) ){
      return NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, mkConcat( kind::STRING_CONCAT, nc1 ), node[1] );
    }

    //splitting
    if( node[1].isConst() ){
      CVC4::String t = node[1].getConst<String>();
      for(unsigned i=1; i<(node[0].getNumChildren()-1); i++){
        //constant contains
        if( node[0][i].isConst() ){
          CVC4::String s = node[0][i].getConst<String>();
          //if no overlap, we can split into disjunction
          if( t.find(s)==std::string::npos ){
            if( s.overlap( t )==0 && t.overlap( s )==0 ){
              std::vector< Node > nc0;
              getConcat( node[0], nc0 );
              std::vector< Node > spl[2];
              spl[0].insert( spl[0].end(), nc0.begin(), nc0.begin()+i );
              Assert( i<nc0.size()-1 );
              spl[1].insert( spl[1].end(), nc0.begin()+i+1, nc0.end() );
              return NodeManager::currentNM()->mkNode( kind::OR,
                          NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, mkConcat( kind::STRING_CONCAT, spl[0] ), node[1] ),
                          NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, mkConcat( kind::STRING_CONCAT, spl[1] ), node[1] ) );
            }
          }
        }
      }
    }
    
  }else if( node[0].getKind()==kind::STRING_SUBSTR ){
    // n>0 => contains( substr( x, n, m ), x ) -> x = ""
    if( node[0][0]==node[1] ){
      if( node[0][1].isConst() && node[0][1].getConst<Rational>().sgn()==1 ){
        //it must be empty string
        return node[1].eqNode( NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
      }
    }
  }
  if( node[1].getKind()==kind::STRING_SUBSTR ){
    if( node[0]==node[1][0] ){
      //contains( x, substr( x, n, m ) ) -> true
      return NodeManager::currentNM()->mkConst( true );
    }
  }
  
  
  //overapproximation of first argument
  Node o_node0 = getApproximation( node[0], false );
  Node u_node1 = getApproximation( node[1], true );
  if( o_node0!=node[0] ){
    // x substr x' ^ ( contains( x', y ) -> false ) => ( contains( x, y ) -> false ) 
    Node cmp_con = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, o_node0, node[1] );
    cmp_con = Rewriter::rewrite( cmp_con );
    if( cmp_con==NodeManager::currentNM()->mkConst(false) ){
      Trace("strings-rewrite-advanced") << "Rewrite " << node << " to false by overapproximation, negative contain entailment." << std::endl;
      return NodeManager::currentNM()->mkConst( false );
    }
  }
  Node u_node0 = getApproximation( node[0], true );
  Node o_node1 = getApproximation( node[1], false );
  if( u_node0!=node[0] ){
    // x' substr x ^ ( contains( x', y ) -> true ) => ( contains( x, y ) -> true ) 
    Node cmp_con = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, u_node0, node[1] );
    cmp_con = Rewriter::rewrite( cmp_con );
    if( cmp_con==NodeManager::currentNM()->mkConst(true) ){
      Trace("strings-rewrite-advanced") << "Rewrite " << node << " to true by underapproximation, positive contain entailment." << std::endl;
      return NodeManager::currentNM()->mkConst( true );
    }
  }
  
  
  //length entailment
  Node l1, u1;
  getLengthEntail( node[0], l1, u1 );
  Node l2, u2;
  getLengthEntail( node[1], l2, u2 );
  Node cmp_len = NodeManager::currentNM()->mkNode( kind::GT, l2, u1 );
  if( entailCheck( cmp_len ) ){
    // second string is longer than first
    Trace("strings-rewrite-advanced") << "Rewrite " << node << " to false since " << l2 << " >= " << u1 << " by length comparison." << std::endl;
    return NodeManager::currentNM()->mkConst( false );
  }
  //TODO : many different length choices

  return node;
}

Node TheoryStringsRewriter::rewriteIndexof( Node node ) {
  if( node[0].isConst() ){
    if( node[0].getConst<String>().size()==0 ){
      return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
    }
  }
  if( node[1].isConst() ){
    if( node[1].getConst<String>().size()==0 ){
      //semantics, change this to node[2]? TODO
      return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
    }
  }
  if( node[2].isConst() ){
    CVC4::Rational RMAXINT(LONG_MAX);
    if( node[2].getConst<Rational>()>RMAXINT ){
      Assert(node[2].getConst<Rational>() <= RMAXINT, "Number exceeds LONG_MAX in string index_of");
      return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
    }else if( node[2].getConst<Rational>().sgn()==-1 ){
      return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
    }else if( node[2].getConst<Rational>().sgn()==1 ){
      if( node[0]==node[1] ){
        return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
      }
    }else if( node[2].getConst<Rational>().sgn()==0 ){
      if( node[0]==node[1] ){
        return node[2];
      }
    }
    if( node[0].isConst() && node[1].isConst() ){
      CVC4::String s = node[0].getConst<String>();
      CVC4::String t = node[1].getConst<String>();
      std::size_t ret = s.find( t, node[2].getConst<Rational>().getNumerator().toUnsignedInt() );
      if( ret==std::string::npos ){
        return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
      }else{
        return NodeManager::currentNM()->mkConst( ::CVC4::Rational(ret) );
      }
    }
  }
  
  // check if contains is entailed
  Node cmp_con = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, node[0], node[1] );
  cmp_con = Rewriter::rewrite( cmp_con );
  if( cmp_con==NodeManager::currentNM()->mkConst(false) ){
    //overapproximation, so definitely false
    Trace("strings-rewrite-advanced") << "Rewrite " << node << " to -1 by negative contain entailment" << std::endl;
    return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
  }else if( cmp_con==NodeManager::currentNM()->mkConst(true) ){
    // TODO 
  }
  
  //get children for node[0], node[1]
  std::vector< Node > children0;
  getConcat( node[0], children0 );
  std::vector< Node > children1;
  getConcat( node[1], children1 );
  
  //strip last component based on non-overlapping constants
  std::vector< Node > cb0;
  std::vector< Node > ce0;
  if( stripConstantEndpoints( children0, children1, cb0, ce0, 1 ) ){
    return NodeManager::currentNM()->mkNode( kind::STRING_STRIDOF, mkConcat( kind::STRING_CONCAT, children0 ), node[1], node[2] );
  }
  
  Node fnode;
  std::vector< Node > sum;
  Node snode;
  if( node[2].isConst() && node[2].getConst<Rational>().sgn()==0 ){
    fnode = node[0];
    snode = node[2];
  }else{
    //speculatively, take substring
    fnode = NodeManager::currentNM()->mkNode( kind::STRING_SUBSTR, node[0], node[2],
               NodeManager::currentNM()->mkNode( kind::MINUS, NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, node[0] ), node[2] ) );
    fnode = Rewriter::rewrite( fnode );
    Trace("strings-rewrite-advanced-debug") << "For " << node << ", speculatively consider rewrites under " << fnode << "..." << std::endl;
    //recompute contains entailment
    cmp_con = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, fnode, node[1] );
    cmp_con = Rewriter::rewrite( cmp_con );
    if( cmp_con==NodeManager::currentNM()->mkConst(false) ){
      Trace("strings-rewrite-advanced") << "Rewrite " << node << " to -1 by negative contain entailment, after considering substr." << std::endl;
      return NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
    }else{
      //return node; // TODO?
      sum.push_back( node[2] );
      snode = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
      children0.clear();
      getConcat( fnode, children0 );
    }
  }
  
  //all rewrites beyond here are for the case that indexof will return >= 0

  // check if positive contains is entailed
  if( cmp_con==NodeManager::currentNM()->mkConst(true) ){
    //component-wise containment
    std::vector< Node > cr;
    int cc = componentContains( children0, children1, cr, true );
    if( cc!=-1 ){
      if( !cr.empty() ){
        //drop remainder past first definite containment
        sum.push_back( NodeManager::currentNM()->mkNode( kind::STRING_STRIDOF, mkConcat( kind::STRING_CONCAT, children0 ), node[1], snode ) );
        Node ret = sum.size()==1 ? sum[0] : NodeManager::currentNM()->mkNode( kind::PLUS, sum );
        Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " due to indexof definite containment." << std::endl;
        return ret;
      }
    }
    // strip first component based on non-overlapping constants
    std::vector< Node > cb;
    std::vector< Node > ce;
    if( stripConstantEndpoints( children0, children1, cb, ce, -1 ) ){
      Assert( cb.size()==1 && cb[0].isConst() );
      sum.push_back( NodeManager::currentNM()->mkConst( ::CVC4::Rational( cb[0].getConst<String>().size() ) ) );
      sum.push_back( NodeManager::currentNM()->mkNode( kind::STRING_STRIDOF, mkConcat( kind::STRING_CONCAT, children0 ), node[1], snode ) );
      Node ret = NodeManager::currentNM()->mkNode( kind::PLUS, sum );
      Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " due to indexof non-overlapping constant prefix + definite containment." << std::endl;
      return ret;
    }
  }

  return node;
}

Node TheoryStringsRewriter::rewriteReplace( Node node ) {
  if( node[1]==node[2] ){
    return node[0];
  }else if( node[0]==node[1] ){
    return node[2];
  }else if( node[1].isConst() ){
    if( node[1].getConst<String>().isEmptyString() ){
      return node[0];
    }
    //if empty, we prepend node[2]
    if( node[1].getConst<String>().size()==0 ){
      return NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, node[2], node[0] );
    }else if( node[0].isConst() ){
      CVC4::String s = node[0].getConst<String>();
      CVC4::String t = node[1].getConst<String>();
      std::size_t p = s.find(t);
      if( p==std::string::npos ){
        return node[0];
      }else{
        CVC4::String s1 = s.substr(0, (int)p);
        CVC4::String s3 = s.substr((int)p + (int)t.size());
        Node ns1 = NodeManager::currentNM()->mkConst( ::CVC4::String(s1) );
        Node ns3 = NodeManager::currentNM()->mkConst( ::CVC4::String(s3) );
        return NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, ns1, node[2], ns3 );
      }
    }
  }else if( node[0].isConst() ){
    if( node[0].getConst<String>().isEmptyString() ){
      return node[0];
    }
  }
  std::vector< Node > children0;
  getConcat( node[0], children0 );
  std::vector< Node > children1;
  getConcat( node[1], children1 );

  //strip first/last component based on non-overlapping constants
  std::vector< Node > cb;
  std::vector< Node > ce;
  if( stripConstantEndpoints( children0, children1, cb, ce ) ){
    std::vector< Node > cc;
    cc.insert( cc.end(), cb.begin(), cb.end() );
    cc.push_back( NodeManager::currentNM()->mkNode( kind::STRING_STRREPL, mkConcat( kind::STRING_CONCAT, children0 ), node[1], node[2] ) );
    cc.insert( cc.end(), ce.begin(), ce.end() );
    return mkConcat( kind::STRING_CONCAT, cc );
  }

  // check if negative contains is entailed
  Node cmp_con = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, node[0], node[1] );
  cmp_con = Rewriter::rewrite( cmp_con );
  if( cmp_con==NodeManager::currentNM()->mkConst(false) ){
    Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << node[0] << " by negative contain entailment" << std::endl;
    return node[0];
  }else if( cmp_con==NodeManager::currentNM()->mkConst(true) ){
    //component-wise containment
    std::vector< Node > cr;
    int cc = componentContains( children0, children1, cr, true );
    if( cc!=-1 ){
      if( !cr.empty() ){
        //strip remainder past first definite containment
        std::vector< Node > cc;
        cc.push_back( NodeManager::currentNM()->mkNode( kind::STRING_STRREPL, mkConcat( kind::STRING_CONCAT, children0 ), node[1], node[2] ) );
        cc.insert( cc.end(), cr.begin(), cr.end() );
        Node ret = mkConcat( kind::STRING_CONCAT, cc );
        Trace("strings-rewrite-advanced") << "Rewrite " << node << " to " << ret << " due to replace definite containment." << std::endl;
        return ret;
      }
    }
  }

  //no rewrites possible
  return node;
}

void TheoryStringsRewriter::getConcat( Node n, std::vector< Node >& c ) {
  if( n.getKind()==kind::STRING_CONCAT || n.getKind()==kind::REGEXP_CONCAT ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      c.push_back( n[i] );
    }
  }else{
    c.push_back( n );
  }
}

Node TheoryStringsRewriter::mkConcat( Kind k, std::vector< Node >& c ){
  Assert( !c.empty() || k==kind::STRING_CONCAT );
  return c.size()>1 ? NodeManager::currentNM()->mkNode( k, c ) : ( c.size()==1 ? c[0] : NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
}

Node TheoryStringsRewriter::splitConstant( Node a, Node b, int& index, bool isRev ) {
  Assert( a.isConst() && b.isConst() );
  index = a.getConst<String>().size() <= b.getConst<String>().size() ? 1 : 0;
  unsigned len_short = index==1 ? a.getConst<String>().size() : b.getConst<String>().size();
  bool cmp = isRev ? a.getConst<String>().rstrncmp(b.getConst<String>(), len_short): a.getConst<String>().strncmp(b.getConst<String>(), len_short);
  if( cmp ) {
    Node l = index==0 ? a : b;
    if( isRev ){
      int new_len = l.getConst<String>().size() - len_short;
      return NodeManager::currentNM()->mkConst(l.getConst<String>().substr( 0, new_len ));
    }else{
      return NodeManager::currentNM()->mkConst(l.getConst<String>().substr( len_short ));
    }
  }else{
    //not the same prefix/suffix
    return Node::null();
  }
}

bool TheoryStringsRewriter::canConstantContainConcat( Node c, Node n, int& firstc, int& lastc ) {
  Assert( c.isConst() );
  CVC4::String t = c.getConst<String>();
  Assert( n.getKind()==kind::STRING_CONCAT );
  //must find constant components in order
  size_t pos = 0;
  firstc = -1;
  lastc = -1;
  for(unsigned i=0; i<n.getNumChildren(); i++) {
    if( n[i].isConst() ){
      firstc = firstc==-1 ? i : firstc;
      lastc = i;
      CVC4::String s = n[i].getConst<String>();
      size_t new_pos = t.find(s,pos);
      if( new_pos==std::string::npos ) {
        return false;
      }else{
        pos = new_pos + s.size();
      }
    }
  }
  return true;

}

// if returns n>0, then n1 = { x1...x{n-1} xn...x{n+s} x{n+s+1}...xm }, n2 = { y1...ys }, where y1 suffix of xn, y2...y{s-1} = x{n+1}...x{n+s-1}, ys is prefix of x{n+s}
//                 if computeRemainder = true, then n1 is updated to { x1...x{n-1} xn...ys }, nr is { ( x{n+s} \ ys ) x{n+s+1}...xm }
int TheoryStringsRewriter::componentContains( std::vector< Node >& n1, std::vector< Node >& n2, std::vector< Node >& nr, bool computeRemainder ){
  if( n2.size()==1 && n2[0].isConst() ){
    CVC4::String t = n2[0].getConst<String>();
    for( unsigned i=0; i<n1.size(); i++ ){
      if( n1[i].isConst() ){
        CVC4::String s = n1[i].getConst<String>();
        size_t f = s.find(t);
        if( f!=std::string::npos ) {
          if( computeRemainder ){
            Assert( s.size()>=f + t.size() );
            if( s.size()>f+t.size() ){
              nr.push_back( NodeManager::currentNM()->mkConst( ::CVC4::String( s.substr( f + t.size(), s.size() - (f + t.size()) ) ) ) );
            }
            nr.insert( nr.end(), n1.begin()+i+1, n1.end() );
            n1[i] = NodeManager::currentNM()->mkConst( ::CVC4::String( s.substr( 0, f + t.size() ) ) );
            n1.erase( n1.begin()+i+1, n1.end() );
          }
          return i;
        }
      }
    }
  }else if( n1.size()>=n2.size() ){
    unsigned diff = n1.size()-n2.size();
    for(unsigned i=0; i<=diff; i++) {
      bool check = false;
      if( n1[i]==n2[0] ){
        check = true;
      }else if( n1[i].isConst() && n2[0].isConst()){
        //could be suffix
        CVC4::String s = n1[i].getConst<String>();
        CVC4::String t =  n2[0].getConst<String>();
        if( t.size()<s.size() && s.suffix(t.size())==t ){
          check = true;
        }
      }
      if( check ){
        bool success = true;
        for(unsigned j=1; j<n2.size(); j++) {
          if( n1[i+j]!=n2[j] ){
            if( j+1==n2.size() && n1[i+j].isConst() && n2[j].isConst() ){
              //could be prefix
              CVC4::String s = n1[i+j].getConst<String>();
              CVC4::String t = n2[j].getConst<String>();
              if( t.size()<s.size() && s.prefix(t.size())==t ){
                if( computeRemainder ){
                  if( s.size()>t.size() ){
                    nr.push_back( NodeManager::currentNM()->mkConst( ::CVC4::String( s.substr( t.size(), s.size() - t.size() ) ) ) );
                  }
                  n1[i+j] = NodeManager::currentNM()->mkConst( ::CVC4::String( s.substr( 0, t.size() ) ) );
                }
              }else{
                success = false;
                break;
              }
            }else{
              success = false;
              break;
            }
          }
        }
        if( success ){
          if( computeRemainder ){
            nr.insert( nr.end(), n1.begin()+i+n2.size(), n1.end() );
            n1.erase( n1.begin()+i+n2.size(), n1.end() );
          }
          return i;
        }
      }
    }
  }
  return -1;
}

bool TheoryStringsRewriter::stripConstantEndpoints( std::vector< Node >& n1, std::vector< Node >& n2,
                                                   std::vector< Node >& nb, std::vector< Node >& ne, int dir ) {
  bool changed = false;
  for( unsigned r=0; r<2; r++ ){
    if( dir==0 || ( r==0 && dir==-1 ) || ( r==1 && dir==1 ) ){
      unsigned index0 = r==0 ? 0 : n1.size()-1;
      unsigned index1 = r==0 ? 0 : n2.size()-1;
      if( n1[index0].isConst() && n2[index1].isConst() ){
        CVC4::String s = n1[index0].getConst<String>();
        CVC4::String t = n2[index1].getConst<String>();
        std::size_t ret = s.find( t );
        if( ret==std::string::npos ) {
          if( n1.size()==1 ){
            //can drop everything : it is not contained
            if( r==0 ){
              nb.push_back( n1[0] );
            }else{
              ne.push_back( n1[0] );
            }
            n1.clear();
            return true;
          }else{
            //check overlap
            if( r==0 ){
              if( s.overlap(t)==0 ){
                //can drop first component
                nb.insert( nb.end(), n1.begin(), n1.begin() + 1 );
                n1.erase( n1.begin(), n1.begin() + 1 );
                changed = true;
              }
            }else{
              Assert( r==1 );
              if( t.overlap(s)==0 ){
                //can drop last argument
                ne.insert( ne.end(), n1.end() - 1, n1.end() );
                n1.erase( n1.end() - 1, n1.end() );
                changed = true;
              }
            }
          }
        }else{
          //inconclusive
        }
      }
    }
  }
  return changed;
}

// if startn > 0 and children[0] = {c0...cn}, then return true, update children[0] = { c{startn}...cn }, startn = max( 0, startn - n )
bool TheoryStringsRewriter::stripConstantPrefix( std::vector< Node >& children, Node& startn ){
  if( !children.empty() && children[0].isConst() ){
    Assert( startn.isConst() );
    Assert( startn.getConst<Rational>() <= Rational(LONG_MAX), "Number exceeds LONG_MAX");
    unsigned start = startn.getConst<Rational>().getNumerator().toUnsignedInt();
    //drop the front
    if( start>0 ){
      CVC4::String t = children[0].getConst<String>();
      if( t.size()>start ){
        children[0] = NodeManager::currentNM()->mkConst( ::CVC4::String( t.substr(start,t.size()-start) ) );
        start = 0;
      }else{
        start = start - t.size();
        children.erase( children.begin(), children.begin() + 1 );
      }
      startn = NodeManager::currentNM()->mkConst( ::CVC4::Rational( start ) );
      return true;
    }
  }
  return false;
}

unsigned TheoryStringsRewriter::stripSymbolicLength( std::vector< Node >& n1, std::vector< Node >& nr, Node& curr_s ) {
  Node zero = NodeManager::currentNM()->mkConst( CVC4::Rational(0) );
  bool success;
  unsigned sindex = 0;
  do{
    success = false;
    if( curr_s!=zero && sindex<n1.size() ){
      Node next_s = NodeManager::currentNM()->mkNode( kind::MINUS, curr_s, NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n1[sindex] ) );
      next_s = Rewriter::rewrite( next_s );
      Node cmp_next_s = NodeManager::currentNM()->mkNode( kind::GEQ, next_s, zero );
      if( entailCheck( cmp_next_s ) ){
        success = true;
        curr_s = next_s;
        sindex++;
      }
    }
  }while( success );
  if( sindex>0 ){
    nr.insert( nr.end(), n1.begin(), n1.begin() + sindex );
    n1.erase( n1.begin(), n1.begin() + sindex );
  }
  return sindex;
}

// return false if c1...cn cannot contain { l1...lm }
bool TheoryStringsRewriter::canConstantContainList( Node c, std::vector< Node >& l, int& firstc, int& lastc ) {
  Assert( c.isConst() );
  CVC4::String t = c.getConst<String>();
  //must find constant components in order
  size_t pos = 0;
  firstc = -1;
  lastc = -1;
  for(unsigned i=0; i<l.size(); i++) {
    if( l[i].isConst() ){
      firstc = firstc==-1 ? i : firstc;
      lastc = i;
      CVC4::String s = l[i].getConst<String>();
      size_t new_pos = t.find(s,pos);
      if( new_pos==std::string::npos ) {
        return false;
      }else{
        pos = new_pos + s.size();
      }
    }
  }
  return true;
}

Node TheoryStringsRewriter::getNextConstantAt( std::vector< Node >& vec, unsigned& start_index, unsigned& end_index, bool isRev ) {
  while( vec.size()>start_index && !vec[ start_index ].isConst() ){
    //return Node::null();
    start_index++;
  }
  if( start_index<vec.size() ){
    end_index = start_index;
    return collectConstantStringAt( vec, end_index, isRev );
  }else{
    return Node::null();
  }
}

Node TheoryStringsRewriter::collectConstantStringAt( std::vector< Node >& vec, unsigned& end_index, bool isRev ) {
  std::vector< Node > c;
  while( vec.size()>end_index && vec[ end_index ].isConst() ){
    c.push_back( vec[ end_index ] );
    end_index++;
    //break;
  }
  if( !c.empty() ){
    if( isRev ){
      std::reverse( c.begin(), c.end() );
    }
    Node cc = Rewriter::rewrite( mkConcat( kind::STRING_CONCAT, c ) );
    Assert( cc.isConst() );
    return cc;
  }else{
    return Node::null();
  }
}
