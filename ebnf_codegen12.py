import sys

import ebnf_semantic

class StateNode(object):
	def __init__(self):
		self.transitions = {}
		self.predecessors = set({})

class StateGraph(object):
	def __init__(self):
		self.entry = None
		self.exits = set({})
		self.forks = set({})

class ExpandedIdentifier(ebnf_semantic.EBNF_Pattern):
	def __init__(self, identifier, subpattern, thread):
		self.identifier = identifier
		self.subpattern = subpattern
		self.thread = thread
		self.offset = 0

	def __repr__(self):
		return "%s(%s, %s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.subpattern), repr(self.thread))

class ReduceAction(ebnf_semantic.EBNF_Pattern):
	def __init__(self, identifier, thread):
		self.identifier = identifier
		self.thread = thread
		self.offset = 0

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.thread))

class ForkAction(ebnf_semantic.EBNF_Pattern):
	def __init__(self):
		self.offset = 0

	def __repr__(self):
		return "%s()"%type(self).__name__

def print_state_graph_recurse(graph, node, cache):
	for symbol, next_node in node.transitions.items():
		if next_node == None:
			continue

		if next_node not in cache["ids"]:
			cache["ids"][next_node] = cache["counter"]
			cache["counter"] += 1
			print_state_graph_recurse(graph, next_node, cache)

	print "state_%d:"%cache["ids"][node]

	for symbol, next_node in node.transitions.items():
		if next_node == None:
			print "\t%s -> None"%repr(symbol)
		else:
			print "\t%s -> state_%d"%(repr(symbol), cache["ids"][next_node])

	print ""

def print_state_graph(graph):
	cache = {"ids": {graph.entry: 0}, "counter": 1}
	print_state_graph_recurse(graph, graph.entry, cache)

def print_state_graphs(graphs, ast_info):
	for identifier, graph in graphs.items():
		print "/* %s = %s */"%(identifier, ast_info.rules[identifier])
		print_state_graph(graph)

def find_nodes(graph):
	visited = set({})
	to_visit = set({graph.entry})

	while to_visit:
		node = to_visit.pop()
		visited.add(node)

		for next_node in node.transitions.values():
			if next_node != None and next_node not in visited:
				to_visit.add(next_node)

	return visited

def copy_graph(graph):
	nodes = find_nodes(graph)
	new_nodes = {node: StateNode() for node in nodes}
	new_nodes[None] = None

	for node in nodes:
		new_nodes[node].transitions = {symbol: new_nodes[next_node] for symbol, next_node in node.transitions.items()}

	entry = new_nodes[graph.entry]
	exits = set({new_nodes[node] for node in graph.exits})
	forks = set({new_nodes[node] for node in graph.forks})
	new_graph = StateGraph()
	new_graph.entry = entry
	new_graph.exits = exits
	new_graph.forks = forks
	return new_graph

def simplify_list(pattern):
	if type(pattern) == ebnf_semantic.Concatenation:
		terms = [term for term in pattern.terms if term != None]

		if len(terms) == 0:
			return None

		if len(terms) == 1:
			return terms[0]

		return ebnf_semantic.Concatenation(terms)
	elif type(pattern) == ebnf_semantic.Alternation:
		clauses = sorted(list(set([clause for clause in pattern.clauses if clause != None])))

		if len(clauses) == 0:
			return None

		if len(clauses) == 1:
			result = clauses[0]
		else:
			result = ebnf_semantic.Alternation(clauses)

		if None in pattern.clauses:
			result = ebnf_semantic.Optional(result)

		return result

	return pattern

def expand_transitions(transitions, cache):
	ast_info = cache["ast_info"]
	clauses = []

	for symbol, next_pattern in transitions.items():
		if type(symbol) == ebnf_semantic.Identifier:
			identifier_pattern = ast_info.rules[symbol.identifier]
			thread = simplify_list(ebnf_semantic.Concatenation([symbol, next_pattern]))
			clause = simplify_list(ebnf_semantic.Concatenation([ExpandedIdentifier(symbol.identifier, identifier_pattern, thread), next_pattern]))
		elif type(symbol) == ExpandedIdentifier:
			subnode = build_state_node(symbol.subpattern, cache)
			clauses1 = []

			for symbol1, next_pattern1 in subnode.transitions.items():
				if type(symbol1) == str:
					symbol2 = ebnf_semantic.Terminal(symbol1)
				else:
					symbol2 = symbol1

				if next_pattern1 == None:
					clause1 = simplify_list(ebnf_semantic.Concatenation([symbol2, ReduceAction(symbol.identifier, symbol.thread)]))
				else:
					clause1 = simplify_list(ebnf_semantic.Concatenation([symbol2, ExpandedIdentifier(symbol.identifier, next_pattern1, symbol.thread)]))

				clauses1.append(clause1)

			clause = simplify_list(ebnf_semantic.Alternation(clauses1))
		elif type(symbol) == ForkAction:
			clause = next_pattern
		elif type(symbol) == str:
			clause = simplify_list(ebnf_semantic.Concatenation([ebnf_semantic.Terminal(symbol), next_pattern]))
		elif symbol == None:
			clause = next_pattern
		else:
			clause = simplify_list(ebnf_semantic.Concatenation([symbol, next_pattern]))

		clauses.append(clause)

	expanded_pattern = simplify_list(ebnf_semantic.Alternation(clauses))
	expanded_pattern = simplify_list(ebnf_semantic.Concatenation([ForkAction(), expanded_pattern]))
	return expanded_pattern

def build_state_node_for_terminal(pattern, cache):
	terminal = pattern.terminal
	node = StateNode()

	if len(terminal) == 1:
		node.transitions = {terminal[0]: None}
	else:
		node.transitions = {terminal[0]: ebnf_semantic.Terminal(terminal[1:])}

	return node

def build_state_node_for_identifier(pattern, cache):
	node = StateNode()
	node.transitions = {pattern: None}
	return node

def build_state_node_for_optional(pattern, cache):
	subnode = build_state_node(pattern.rhs, cache)
	transitions = {symbol: next_pattern for symbol, next_pattern in subnode.transitions.items()}

	if None in transitions and transitions[None] != None:
		transitions[None] = ebnf_semantic.Optional(transitions[None])
	else:
		transitions[None] = None

	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_repetition(pattern, cache):
	subnode = build_state_node(pattern.rhs, cache)
	transitions = {symbol: simplify_list(ebnf_semantic.Concatenation([next_pattern, pattern])) for symbol, next_pattern in subnode.transitions.items()}

	if None in transitions and transitions[None] != None:
		transitions[None] = ebnf_semantic.Repetition(transitions[None])
	else:
		transitions[None] = None

	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_concatenation(pattern, cache):
	terms = list(pattern.terms)
	subnode = build_state_node(terms[0], cache)
	transitions = {symbol: simplify_list(ebnf_semantic.Concatenation([next_pattern] + terms[1:])) for symbol, next_pattern in subnode.transitions.items() if symbol != None}

	if None in subnode.transitions:
		clauses = []

		for symbol, next_pattern in transitions.items():
			if type(symbol) == str:
				clauses.append(simplify_list(ebnf_semantic.Concatenation([ebnf_semantic.Terminal(symbol), next_pattern])))
			else:
				clauses.append(simplify_list(ebnf_semantic.Concatenation([symbol, next_pattern])))

		clauses.append(simplify_list(ebnf_semantic.Concatenation([subnode.transitions[None]] + terms[1:])))
		simplified_pattern = simplify_list(ebnf_semantic.Alternation(clauses))
		return build_state_node(simplified_pattern, cache)

	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_alternation(pattern, cache):
	subnodes = [build_state_node(clause, cache) for clause in pattern.clauses]
	transitions_clauses = {}

	for subnode in subnodes:
		for symbol, next_pattern in subnode.transitions.items():
			if symbol not in transitions_clauses:
				transitions_clauses[symbol] = []

			transitions_clauses[symbol].append(next_pattern)

	transitions = {symbol: simplify_list(ebnf_semantic.Alternation(clauses)) for symbol, clauses in transitions_clauses.items()}
	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_expanded_identifier(pattern, cache):
	transitions = {pattern: None}
	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_reduce_action(pattern, cache):
	transitions = {pattern: None}
	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_fork_action(pattern, cache):
	transitions = {pattern: None}
	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node(pattern, cache):
	if pattern not in cache["nodes"]:
		builders = {ebnf_semantic.Terminal: build_state_node_for_terminal,
				ebnf_semantic.Identifier: build_state_node_for_identifier,
				ebnf_semantic.Optional: build_state_node_for_optional,
				ebnf_semantic.Repetition: build_state_node_for_repetition,
				ebnf_semantic.Concatenation: build_state_node_for_concatenation,
				ebnf_semantic.Alternation: build_state_node_for_alternation,
				ExpandedIdentifier: build_state_node_for_expanded_identifier,
				ReduceAction: build_state_node_for_reduce_action,
				ForkAction: build_state_node_for_fork_action}

		node = builders[type(pattern)](pattern, cache)
		transitions = node.transitions

		if len(transitions) > 1:
			types = map(type, transitions.keys())
			expandable_types = [ebnf_semantic.Identifier, ExpandedIdentifier, ForkAction]

			if any([x in types for x in expandable_types]):
				expanded_pattern = expand_transitions(transitions, cache)
				node = build_state_node(expanded_pattern, cache)

		cache["nodes"][pattern] = node

	return cache["nodes"][pattern]

def build_state_graph(pattern, cache):
	if pattern not in cache["graphs"]:
		node = StateNode()
		graph = StateGraph()
		graph.entry = node
		cache["graphs"][pattern] = graph

		entrynode = build_state_node(pattern, cache)

		if ForkAction in map(type, entrynode.transitions.keys()):
			graph.forks.add(node)

		for symbol, next_pattern in entrynode.transitions.items():
			if next_pattern == None:
				node.transitions[symbol] = None
				graph.exits.add(node)
			else:
				subgraph = build_state_graph(next_pattern, cache)
				node.transitions[symbol] = subgraph.entry
				graph.exits.update(subgraph.exits)
				graph.forks.update(subgraph.forks)

	return cache["graphs"][pattern]

def gen_predecessors(graph):
	to_visit = set({graph.entry})
	visited = set({})

	while to_visit:
		node = to_visit.pop()
		visited.add(node)

		for symbol, next_node in node.transitions.items():
			if next_node != None:
				next_node.predecessors.add((node, symbol))

				if next_node not in visited:
					to_visit.add(next_node)

def merge_common_nodes(graph):
	to_visit = graph.exits
	visited = set({})
	changed = False

	while to_visit:
		nodesets = {}
		visited.update(to_visit)

		for node in to_visit:
			if repr(node.transitions) not in nodesets:
				nodesets[repr(node.transitions)] = set({})

			nodesets[repr(node.transitions)].add(node)

		to_visit = set({})

		for nodeset in nodesets.values():
			if len(nodeset) > 1:
				changed = True
				node = list(nodeset)[0]
				node.predecessors = set.union(*[x.predecessors for x in nodeset])

				for prev_node, symbol in node.predecessors:
					prev_node.transitions[symbol] = node

				if graph.entry in nodeset:
					graph.entry = node

				graph.forks -= nodeset - set({node})
				graph.exits -= nodeset - set({node})
				to_visit.update(set({prev_node for prev_node, symbol in node.predecessors if prev_node not in visited}))

	return changed

def merge_fork_nodes(graph):
	changed = False
	new_forks = set({})

	for node in graph.forks:
		if node.transitions[ForkAction()] in graph.forks:
			changed = True

			for prev_node, symbol in node.predecessors:
				prev_node.transitions[symbol] = node.transitions[ForkAction()]
				node.transitions[ForkAction()].predecessors.discard((node, ForkAction()))
				node.transitions[ForkAction()].predecessors.add((prev_node, symbol))

			if graph.entry == node:
				graph.entry = node.transitions[ForkAction()]
		else:
			new_forks.add(node)

	graph.forks = new_forks
	return changed

def minimize_state_graph(graph):
	changed = True

	while changed:
		changed = merge_fork_nodes(graph) or merge_common_nodes(graph)

def build_state_graphs(ast_info):
	cache = {"graphs": {}, "nodes": {}, "ast_info": ast_info}
	graphs = {identifier: copy_graph(build_state_graph(pattern, cache)) for identifier, pattern in ast_info.rules.items()}

	for graph in graphs.values():
		gen_predecessors(graph)
		minimize_state_graph(graph)

	return graphs

if len(sys.argv) != 3:
	print "Usage: %s <grammar file> <top_id>"%(sys.argv[0])
	quit()

filename = sys.argv[1]
top_id = sys.argv[2]

with open(filename, 'r') as f:
	description = f.read()

ast_info = ebnf_semantic.create_ast(description, top_id)
graphs = build_state_graphs(ast_info)
print_state_graphs(graphs, ast_info)
