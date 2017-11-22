import sys

import ebnf_semantic

class StateNode(object):
	# case label:
	# 	switch (block[i]) {
	#		case c (c in cases): next_state = $TO_STATE_ENUM(cases[c]);
	#		default: next_state = $TO_STATE_ENUM(cases[None]);
	# 	}
	#
	#	break;
	def __init__(self):
		self.uid = id(self)
		self.cases = None

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.uid), repr(self.cases))

	def pretty_print(self, labels):
		print "state_%s:"%labels[self.uid]
		print "\tswitch (c) {"

		for cinput in self.cases:
			if cinput == None:
				continue
			else:
				print "\t\tcase %s: goto state_%s;"%(repr(cinput), labels[self.cases[cinput]])

		if None in self.cases:
			print "\t\tdefault: goto state_%s;"%(labels[self.cases[None]])

		print "\t}\n"

class StateGraph(object):
	def __init__(self, nodes, entry, success_edges, error_edges):
		self.nodes = nodes
		self.entry = entry
		self.success_edges = success_edges
		self.error_edges = error_edges

	def __repr__(self):
		return "%s(%s, %s, %s, %s)"%(type(self).__name__, repr(self.nodes), repr(self.entry), repr(self.success_edges), repr(self.error_edges))

	def pretty_print(self):
		labels = {}

		for i, state in enumerate(self.nodes):
			labels[state] = str(i)

		labels["success"] = "success"
		labels["error"] = "error"

		print "entry label: state_%s\n"%labels[self.entry]

		for state in self.nodes:
			self.nodes[state].pretty_print(labels)

def replace_success_with_error(graph):
	for state, cinput in graph.success_edges:
		graph.nodes[state].cases[cinput] = "error"

	graph.error_edges.extend(graph.success_edges)
	graph.success_edges = []

def merge_optionals_and_repetitions(pattern, subgraphs):
	merged_subgraphs = []
	i = 0

	while i < len(pattern.terms):
		term = pattern.terms[i]
		subgraph = subgraphs[i]
		i += 1

		while i < len(pattern.terms) and type(term) in [ebnf_semantic.Optional, ebnf_semantic.Repetition]:
			term = pattern.terms[i]

			if type(term) not in [ebnf_semantic.Optional, ebnf_semantic.Repetition]:
				replace_success_with_error(subgraph)

			subgraph = merge_graphs([subgraph, subgraphs[i]])
			i += 1

		merged_subgraphs.append(subgraph)

	return merged_subgraphs

def merge_cases_list(cases_list):
	new_cases = {}

	for cases, graph in cases_list:
		for cinput, state in cases.items():
			if cinput not in new_cases:
				new_cases[cinput] = []

			if state != "error":
				new_cases[cinput].append((graph, state))

	for cinput in new_cases:
		for graph, state in new_cases[cinput]:
			if state == "success":
				new_cases[cinput] = [(graph, "success")]
				break

	return new_cases

def minimize_graph(graph):
	# Last step of merging, minimize the DFA by combining common states
	back_edges = {}

	for state in graph.nodes:
		cases = graph.nodes[state].cases

		for cinput in cases:
			next_state = cases[cinput]

			if next_state not in back_edges:
				back_edges[next_state] = {}

			if state not in back_edges[next_state]:
				back_edges[next_state][state] = []

			back_edges[next_state][state].append(cinput)

	back_edges["success"] = {}

	for state, cinput in graph.success_edges:
		if state not in back_edges["success"]:
			back_edges["success"][state] = []

		back_edges["success"][state].append(cinput)

	back_edges["error"] = {}

	for state, cinput in graph.error_edges:
		if state not in back_edges["error"]:
			back_edges["error"][state] = []

		back_edges["error"][state].append(cinput)

	merge_stack = ["success", "error"]

	while merge_stack:
		merged_state = merge_stack.pop()
		predecessors = back_edges[merged_state]
		replacements = {}
		cache = {}

		for state in predecessors:
			state_cases = frozenset(graph.nodes[state].cases.items())

			if state_cases not in cache:
				cache[state_cases] = state
			else:
				replacements[state] = cache[state_cases]

				if cache[state_cases] not in merge_stack:
					merge_stack.append(cache[state_cases])

		for state in replacements:
			for prev_state in back_edges[state]:
				if prev_state in graph.nodes:
					for cinput in back_edges[state][prev_state]:
						graph.nodes[prev_state].cases[cinput] = replacements[state]

			for cinput, next_state in graph.nodes[state].cases.items():
				del back_edges[next_state][state]

				if replacements[state] not in back_edges[next_state]:
					back_edges[next_state][replacements[state]] = []

				back_edges[next_state][replacements[state]].append(cinput)

			del graph.nodes[state]

	graph.success_edges = [(state, cinput) for state, cinput in graph.success_edges if state in graph.nodes]
	graph.error_edges = [(state, cinput) for state, cinput in graph.error_edges if state in graph.nodes]

def merge_graphs(graphs):
	# Convert from NDFA to DFA and then minimize
	nodes = graphs[0].nodes
	entry = graphs[0].entry
	success_edges = []
	error_edges = []

	entry_node = graphs[0].nodes[entry]

	merge_stack = []
	node_stack = []

	merge_stack.append([(graph, graph.entry) for graph in graphs])
	node_stack.append(entry_node)
	merge_cache = set({})

	while merge_stack:
		states_to_merge = merge_stack.pop()
		node = node_stack.pop()

		state_tuple = tuple([state for graph, state in states_to_merge])

		if (state_tuple, node) in merge_cache:
			continue

		merge_cache.add((state_tuple, node))

		cases_choices = merge_cases_list([(graph.nodes[state].cases, graph) for graph, state in states_to_merge])
		nodes[node.uid] = node

		for cinput in cases_choices:
			if len(cases_choices[cinput]) == 0:
				node.cases[cinput] = "error"
				error_edges.append((node.uid, cinput))
			elif set([state for graph, state in cases_choices[cinput]]) == set(["success"]):
				node.cases[cinput] = "success"
				success_edges.append((node.uid, cinput))
			else:
				graph, state = cases_choices[cinput][0]
				new_node = graph.nodes[state]
				node.cases[cinput] = new_node.uid
				merge_stack.append(cases_choices[cinput])
				node_stack.append(new_node)

	new_graph = StateGraph(nodes, entry, success_edges, error_edges)
	minimize_graph(new_graph)

	return new_graph

def build_state_graph_for_terminal(pattern, ast_info):
	terminal = pattern.terminal

	nodes = {}
	error_edges = []

	concat_nodes = [StateNode() for i in range(len(terminal))]

	for i in range(len(terminal) - 1):
		node = concat_nodes[i]
		node.cases = {terminal[i]: concat_nodes[i + 1].uid, None: "error"}

		nodes[node.uid] = node
		error_edges.append((node.uid, None))

	node = concat_nodes[-1]
	node.cases = {terminal[-1]: "success", None: "error"}

	nodes[node.uid] = node
	success_edges = [(node.uid, terminal[-1])]
	error_edges.append((node.uid, None))

	entry = concat_nodes[0].uid

	return StateGraph(nodes, entry, success_edges, error_edges)

def build_state_graph_for_optional(pattern, ast_info):
	subgraph = build_state_graph_demux(pattern.rhs, ast_info)

	for edge in subgraph.error_edges:
		state = edge[0]
		cinput = edge[1]
		subgraph.nodes[state].cases[cinput] = "success"
		subgraph.success_edges.append(edge)

	subgraph.error_edges = []
	return subgraph

def build_state_graph_for_repetition(pattern, ast_info):
	subgraph = build_state_graph_demux(pattern.rhs, ast_info)

	for edge in subgraph.success_edges:
		state = edge[0]
		cinput = edge[1]
		subgraph.nodes[state].cases[cinput] = subgraph.entry

	success_edges = []

	for edge in subgraph.error_edges:
		state = edge[0]
		cinput = edge[1]
		subgraph.nodes[state].cases[cinput] = "success"
		success_edges.append(edge)

	subgraph.success_edges = success_edges
	subgraph.error_edges = []
	return subgraph

def build_state_graph_for_concatenation(pattern, ast_info):
	subgraphs = [build_state_graph_demux(term, ast_info) for term in pattern.terms]
	subgraphs = merge_optionals_and_repetitions(pattern, subgraphs)

	nodes = {}
	error_edges = []

	for i in range(len(subgraphs) - 1):
		term = pattern.terms[i]
		subgraph = subgraphs[i]
		next_subgraph = subgraphs[i + 1]

		for state, cinput in subgraph.success_edges:
			subgraph.nodes[state].cases[cinput] = next_subgraph.entry

		error_edges.extend(subgraph.error_edges)
		nodes.update(subgraph.nodes)

	nodes.update(subgraphs[-1].nodes)
	entry = subgraphs[0].entry
	success_edges = subgraphs[-1].success_edges
	error_edges.extend(subgraphs[-1].error_edges)

	return StateGraph(nodes, entry, success_edges, error_edges)

def build_state_graph_for_alternation(pattern, ast_info):
	graphs = [build_state_graph_demux(clause, ast_info) for clause in pattern.clauses]
	return merge_graphs(graphs)

def build_state_graph_demux(pattern, ast_info):
	builders = {ebnf_semantic.Alternation: build_state_graph_for_alternation,
			ebnf_semantic.Concatenation: build_state_graph_for_concatenation,
			ebnf_semantic.Repetition: build_state_graph_for_repetition,
			ebnf_semantic.Optional: build_state_graph_for_optional,
			ebnf_semantic.Terminal: build_state_graph_for_terminal}

	return builders[type(pattern)](pattern, ast_info)

def build_state_graph(ast_info):
	return build_state_graph_demux(ast_info.rules[ast_info.top_id], ast_info)

if len(sys.argv) != 3:
	print "Usage: %s <grammar file> <top_id>"%(sys.argv[0])
	quit()

filename = sys.argv[1]
top_id = sys.argv[2]

with open(filename, 'r') as f:
	description = f.read()

ast_info = ebnf_semantic.create_ast(description, top_id)

graph = build_state_graph(ast_info)
graph.pretty_print()
