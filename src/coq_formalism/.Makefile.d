utilities.vo utilities.glob utilities.v.beautified utilities.required_vo: utilities.v 
utilities.vio: utilities.v 
utilities.vos utilities.vok utilities.required_vos: utilities.v 
attack_graph.vo attack_graph.glob attack_graph.v.beautified attack_graph.required_vo: attack_graph.v 
attack_graph.vio: attack_graph.v 
attack_graph.vos attack_graph.vok attack_graph.required_vos: attack_graph.v 
graph_normalization.vo graph_normalization.glob graph_normalization.v.beautified graph_normalization.required_vo: graph_normalization.v attack_graph.vo utilities.vo
graph_normalization.vio: graph_normalization.v attack_graph.vio utilities.vio
graph_normalization.vos graph_normalization.vok graph_normalization.required_vos: graph_normalization.v attack_graph.vos utilities.vos
graph_strict_partial_order.vo graph_strict_partial_order.glob graph_strict_partial_order.v.beautified graph_strict_partial_order.required_vo: graph_strict_partial_order.v attack_graph.vo utilities.vo
graph_strict_partial_order.vio: graph_strict_partial_order.v attack_graph.vio utilities.vio
graph_strict_partial_order.vos graph_strict_partial_order.vok graph_strict_partial_order.required_vos: graph_strict_partial_order.v attack_graph.vos utilities.vos
graph_equiv.vo graph_equiv.glob graph_equiv.v.beautified graph_equiv.required_vo: graph_equiv.v utilities.vo attack_graph.vo graph_normalization.vo graph_strict_partial_order.vo
graph_equiv.vio: graph_equiv.v utilities.vio attack_graph.vio graph_normalization.vio graph_strict_partial_order.vio
graph_equiv.vos graph_equiv.vok graph_equiv.required_vos: graph_equiv.v utilities.vos attack_graph.vos graph_normalization.vos graph_strict_partial_order.vos
graph_partial_order.vo graph_partial_order.glob graph_partial_order.v.beautified graph_partial_order.required_vo: graph_partial_order.v attack_graph.vo graph_strict_partial_order.vo graph_normalization.vo graph_equiv.vo utilities.vo
graph_partial_order.vio: graph_partial_order.v attack_graph.vio graph_strict_partial_order.vio graph_normalization.vio graph_equiv.vio utilities.vio
graph_partial_order.vos graph_partial_order.vok graph_partial_order.required_vos: graph_partial_order.v attack_graph.vos graph_strict_partial_order.vos graph_normalization.vos graph_equiv.vos utilities.vos
supports_facts.vo supports_facts.glob supports_facts.v.beautified supports_facts.required_vo: supports_facts.v attack_graph.vo graph_strict_partial_order.vo graph_normalization.vo graph_equiv.vo utilities.vo
supports_facts.vio: supports_facts.v attack_graph.vio graph_strict_partial_order.vio graph_normalization.vio graph_equiv.vio utilities.vio
supports_facts.vos supports_facts.vok supports_facts.required_vos: supports_facts.v attack_graph.vos graph_strict_partial_order.vos graph_normalization.vos graph_equiv.vos utilities.vos
set_equiv.vo set_equiv.glob set_equiv.v.beautified set_equiv.required_vo: set_equiv.v attack_graph.vo graph_strict_partial_order.vo graph_normalization.vo graph_equiv.vo utilities.vo graph_partial_order.vo supports_facts.vo
set_equiv.vio: set_equiv.v attack_graph.vio graph_strict_partial_order.vio graph_normalization.vio graph_equiv.vio utilities.vio graph_partial_order.vio supports_facts.vio
set_equiv.vos set_equiv.vok set_equiv.required_vos: set_equiv.v attack_graph.vos graph_strict_partial_order.vos graph_normalization.vos graph_equiv.vos utilities.vos graph_partial_order.vos supports_facts.vos
set_order.vo set_order.glob set_order.v.beautified set_order.required_vo: set_order.v attack_graph.vo graph_strict_partial_order.vo graph_normalization.vo graph_equiv.vo utilities.vo graph_partial_order.vo supports_facts.vo set_equiv.vo
set_order.vio: set_order.v attack_graph.vio graph_strict_partial_order.vio graph_normalization.vio graph_equiv.vio utilities.vio graph_partial_order.vio supports_facts.vio set_equiv.vio
set_order.vos set_order.vok set_order.required_vos: set_order.v attack_graph.vos graph_strict_partial_order.vos graph_normalization.vos graph_equiv.vos utilities.vos graph_partial_order.vos supports_facts.vos set_equiv.vos
compare.vo compare.glob compare.v.beautified compare.required_vo: compare.v attack_graph.vo graph_strict_partial_order.vo graph_normalization.vo graph_equiv.vo utilities.vo graph_partial_order.vo set_equiv.vo set_order.vo
compare.vio: compare.v attack_graph.vio graph_strict_partial_order.vio graph_normalization.vio graph_equiv.vio utilities.vio graph_partial_order.vio set_equiv.vio set_order.vio
compare.vos compare.vok compare.required_vos: compare.v attack_graph.vos graph_strict_partial_order.vos graph_normalization.vos graph_equiv.vos utilities.vos graph_partial_order.vos set_equiv.vos set_order.vos
