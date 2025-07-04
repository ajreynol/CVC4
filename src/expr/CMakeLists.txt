###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, José Neto, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

libcvc5_add_sources(
  aci_norm.cpp
  aci_norm.h
  algorithm/flatten.h
  annotation_elim_node_converter.cpp
  annotation_elim_node_converter.h
  array_store_all.cpp
  array_store_all.h
  ascription_type.cpp
  ascription_type.h
  attribute.h
  attribute.cpp
  attribute_internals.h
  attribute_unique_id.h
  bound_var_id.cpp
  bound_var_id.h
  bound_var_manager.cpp
  bound_var_manager.h
  cardinality_constraint.cpp
  cardinality_constraint.h
  codatatype_bound_variable.cpp
  codatatype_bound_variable.h
  elim_shadow_converter.cpp
  elim_shadow_converter.h
  elim_witness_converter.cpp
  elim_witness_converter.h
  emptyset.cpp
  emptyset.h
  emptybag.cpp
  emptybag.h
  free_var_cache.cpp
  free_var_cache.h
  function_array_const.cpp
  function_array_const.h
  internal_skolem_id.cpp
  internal_skolem_id.h
  kind_map.h
  match_trie.cpp
  match_trie.h
  nary_match_trie.cpp
  nary_match_trie.h
  nary_term_util.cpp
  nary_term_util.h
  node.cpp
  node.h
  node_algorithm.cpp
  node_algorithm.h
  node_builder.cpp
  node_builder.h
  node_converter.cpp
  node_converter.h
  node_manager_attributes.h
  node_self_iterator.h
  node_trie.cpp
  node_trie.h
  node_trie_algorithm.cpp
  node_trie_algorithm.h
  node_traversal.cpp
  node_traversal.h
  node_value.cpp
  node_value.h
  oracle.h
  oracle_caller.cpp
  oracle_caller.h
  plugin.cpp
  plugin.h
  sequence.cpp
  sequence.h
  node_visitor.h
  skolem_manager.cpp
  skolem_manager.h
  sort_type_size.cpp
  sort_type_size.h
  subtype_elim_node_converter.cpp
  subtype_elim_node_converter.h
  term_canonize.cpp
  term_canonize.h
  term_context.cpp
  term_context.h
  term_context_node.cpp
  term_context_node.h
  term_context_stack.cpp
  term_context_stack.h
  type_checker.h
  type_matcher.cpp
  type_matcher.h
  type_node.cpp
  type_node.h
  dtype.h
  dtype.cpp
  dtype_cons.h
  dtype_cons.cpp
  dtype_selector.h
  dtype_selector.cpp
  sequence.cpp
  sequence.h
  sort_to_term.cpp
  sort_to_term.h
  subs.cpp
  subs.h
  sygus_datatype.cpp
  sygus_datatype.h
  sygus_grammar.cpp
  sygus_grammar.h
  sygus_term_enumerator.cpp
  sygus_term_enumerator.h
  variadic_trie.cpp
  variadic_trie.h
  non_closed_node_converter.cpp
  non_closed_node_converter.h
)

libcvc5_add_sources(GENERATED
  kind.cpp
  kind.h
  metakind.cpp
  metakind.h
  node_manager.cpp
  node_manager.h
  type_checker.cpp
  type_properties.cpp
  type_properties.h
)

#
# Generate code for kinds.
#

set(mkkind_script ${CMAKE_CURRENT_LIST_DIR}/mkkind.py)
set(mkmetakind_script ${CMAKE_CURRENT_LIST_DIR}/mkmetakind.py)
set(mkexpr_script ${CMAKE_CURRENT_LIST_DIR}/mkexpr.py)

add_custom_command(
  OUTPUT kind.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mkkind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/kind_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/kind.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkkind.py kind_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT kind.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mkkind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/kind_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/kind.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkkind.py kind_template.cpp kind.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT type_properties.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mkkind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/type_properties_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/type_properties.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkkind.py type_properties_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT type_properties.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mkkind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/type_properties_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/type_properties.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkkind.py type_properties_template.cpp type_properties.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT metakind.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mkmetakind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/metakind_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/metakind.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkmetakind.py metakind_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT metakind.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mkmetakind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/metakind_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/metakind.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkmetakind.py metakind_template.cpp metakind.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT node_manager.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mkmetakind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/node_manager_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/node_manager.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkmetakind.py node_manager_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT node_manager.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mkmetakind_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/node_manager_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/node_manager.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkmetakind.py node_manager_template.cpp node_manager.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT type_checker.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mkexpr_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/type_checker_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/type_checker.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkexpr.py type_checker_template.cpp ${KINDS_TOML_FILES}
)

add_custom_target(gen-expr
  DEPENDS
    kind.cpp
    kind.h
    metakind.cpp
    metakind.h
    node_manager.cpp
    node_manager.h
    type_checker.cpp
    type_properties.cpp
    type_properties.h
)
