import sys

import ebnf_semantic

class StateNode(object):
	def __init__(self):
		self.uid = id(self)
		self.transitions = {}

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.uid), repr(self.transitions))

	def pretty_print(self, labels, caches, ast_info):
		print "state_%s:"%labels[self.uid]

		if ebnf_semantic.Identifier in map(type, self.transitions.keys()):
			for c, next_state in self.transitions.items():
				if c == None:
					continue

				print "\tif (parse_%s())"%c.identifier
				print "\t\tgoto state_%s;"%labels[next_state]

			print "\telse"
			print "\t\tgoto error;"
			print ""
		elif PartialIdentifier in map(type, self.transitions.keys()):
			for c, next_state in self.transitions.items():
				if c == None:
					continue

				if c.subpattern == None:
					print "\tif (parse_%s(%s, state_success))"%(c.identifier, str(c.accumulator))
					print "\t\tgoto state_%s;"%labels[next_state]
				else:
					subpat_graph = caches[c.identifier]["graphs"][c.subpattern]
					ident_graph = caches[c.identifier]["graphs"][ast_info.rules[c.identifier]]

					print "\tif (parse_%s(%s, state_%s))"%(c.identifier, str(c.accumulator), ident_graph.labels[subpat_graph.entry])
					print "\t\tgoto state_%s;"%labels[next_state]

			print "\telse"
			print "\t\tgoto error;"
			print ""
		else:
			print "\tif (EOF())"

			if None in self.transitions:
				print "\t\tgoto state_%s;\n"%labels[self.transitions[None]]
			else:
				print "\t\tgoto error;\n"

			print "\tswitch (c) {"

			for c, next_state in self.transitions.items():
				if c == None:
					continue

				print "\t\tcase '%s':"%c
				print "\t\t\tgoto state_%s;"%labels[next_state]

			print "\t\tdefault:"
			print "\t\t\tgoto error;"
			print "\t}\n"

class StateGraph(object):
	def __init__(self, nodes, entry):
		self.nodes = nodes
		self.entry = entry
		self.labels = {}
		self.inited = False

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.nodes), repr(self.entry))

	def init_labels(self):
		if not self.inited:
			for i, state in enumerate(self.nodes):
				self.labels[state] = str(i)

			self.labels[None] = "success"
			self.inited = True

	def pretty_print(self, caches, ast_info):
		self.init_labels()

		print "\tgoto state_%s;\n"%self.labels[self.entry]

		for state in self.nodes:
			self.nodes[state].pretty_print(self.labels, caches, ast_info)

class PartialIdentifier(ebnf_semantic.EBNF_Pattern):
	def __init__(self, identifier, accumulator, subpattern):
		self.identifier = identifier
		self.accumulator = accumulator
		self.subpattern = subpattern
		self.offset = 0

	def __repr__(self):
		return "%s(%s, %s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.accumulator), repr(self.subpattern))

def expand_map(prefix_map, ast_info, cache):
	if None in prefix_map:
		return merge_maps(expand_map({c: subpattern for c, subpattern in prefix_map.items() if c != None}, ast_info, cache), {None: prefix_map[None]}, ast_info, cache)

	pattern = prefix_map.keys()[0]

	if type(pattern) == ebnf_semantic.Identifier:
		prefix_map = get_prefix_map(ast_info.rules[pattern.identifier], ast_info, cache)
		new_map = {}

		for c, subpattern in prefix_map.items():
			if c == None:
				new_map[c] = PartialIdentifier(pattern.identifier, 0, subpattern)
			else:
				new_map[c] = PartialIdentifier(pattern.identifier, 1, subpattern)
	else:
		if pattern.subpattern == None:
			next_pattern = prefix_map[pattern]

			if next_pattern == None:
				new_map = {None: None}
			else:
				prefix_map = get_prefix_map(next_pattern, ast_info, cache)
				new_map = {}

				for c, subpattern in prefix_map.items():
					if subpattern == None:
						new_map[c] = pattern
					else:
						new_map[c] = ebnf_semantic.Concatenation([pattern, subpattern], pattern.offset)
		else:
			prefix_map = get_prefix_map(pattern.subpattern, ast_info, cache)
			new_map = {}

			for c, subpattern in prefix_map.items():
				if c == None:
					new_map[c] = PartialIdentifier(pattern.identifier, pattern.accumulator, subpattern)
				else:
					new_map[c] = PartialIdentifier(pattern.identifier, pattern.accumulator + 1, subpattern)

	return new_map

# XXX expand_for_concatenation, expand_for_merge?
def expand_if_optional(pattern, ast_info, cache):
	if type(pattern) == ebnf_semantic.Identifier:
		prefix_map = get_prefix_map(ast_info.rules[pattern.identifier], ast_info, cache)

		if None in prefix_map:
			new_map = {}

			for c, subpattern in prefix_map.items():
				if c == None:
					new_map[c] = PartialIdentifier(pattern.identifier, 0, subpattern)
				else:
					new_map[c] = PartialIdentifier(pattern.identifier, 1, subpattern)

			return new_map, True, False
	elif type(pattern) == PartialIdentifier:
		if pattern.subpattern == None:
			return None, False, False

		# XXX Have a is_circular function
		prefix_map = get_prefix_map(pattern.subpattern, ast_info, cache)

		if None in prefix_map:
			new_map = {}

			for c, subpattern in prefix_map.items():
				if c == None:
					new_map[c] = PartialIdentifier(pattern.identifier, pattern.accumulator, subpattern)
				else:
					new_map[c] = PartialIdentifier(pattern.identifier, pattern.accumulator + 1, subpattern)

			return new_map, True, False

	return None, False, False

def merge_maps(prefix_map1, prefix_map2, ast_info, cache):
	if ebnf_semantic.Identifier in map(type, prefix_map1.keys()) and ebnf_semantic.Identifier in map(type, prefix_map2.keys()):
		identkey1 = None
		identkey2 = None

		for c in prefix_map1.keys():
			if type(c) == ebnf_semantic.Identifier:
				identkey1 = c
				break

		for c in prefix_map2.keys():
			if type(c) == ebnf_semantic.Identifier:
				identkey2 = c
				break

		if identkey1 != identkey2:
			expanded_map1 = expand_map(prefix_map1, ast_info, cache)
			expanded_map2 = expand_map(prefix_map2, ast_info, cache)

			return merge_maps(expanded_map1, expanded_map2, ast_info, cache)
	elif PartialIdentifier in map(type, prefix_map1.keys()) and PartialIdentifier in map(type, prefix_map2.keys()):
		identkey1 = None
		identkey2 = None

		for c in prefix_map1.keys():
			if type(c) == PartialIdentifier:
				identkey1 = c
				break

		for c in prefix_map2.keys():
			if type(c) == PartialIdentifier:
				identkey2 = c
				break

		if identkey1 != identkey2:
			expanded_map1 = expand_map(prefix_map1, ast_info, cache)
			expanded_map2 = expand_map(prefix_map2, ast_info, cache)

			return merge_maps(expanded_map1, expanded_map2, ast_info, cache)
	elif ebnf_semantic.Identifier in map(type, prefix_map1.keys()) or PartialIdentifier in map(type, prefix_map1.keys()):
		expanded_map1 = expand_map(prefix_map1, ast_info, cache)
		return merge_maps(expanded_map1, prefix_map2, ast_info, cache)
	elif ebnf_semantic.Identifier in map(type, prefix_map2.keys()) or PartialIdentifier in map(type, prefix_map2.keys()):
		expanded_map2 = expand_map(prefix_map2, ast_info, cache)
		return merge_maps(prefix_map1, expanded_map2, ast_info, cache)
	else:
		new_map = {}

		for c in prefix_map1:
			if c in prefix_map2:
				subpattern1 = prefix_map1[c]
				subpattern2 = prefix_map2[c]

				if subpattern1 == None:
					if subpattern2 == None:
						new_map[c] = None
					else:
						new_map[c] = ebnf_semantic.Optional(subpattern2, subpattern2.offset)
				else:
					if subpattern2 == None:
						new_map[c] = ebnf_semantic.Optional(subpattern1, subpattern1.offset)
					else:
						new_map[c] = ebnf_semantic.Alternation([subpattern1, subpattern2], subpattern1.offset)
			else:
				new_map[c] = prefix_map1[c]

		for c in prefix_map2:
			if c not in prefix_map1:
				new_map[c] = prefix_map2[c]

		return new_map

def concatenate_to_map(prefix_map, terms, ast_info, cache):
	if None in prefix_map:
		if len(terms) == 1:
			next_pattern = terms[0]
		else:
			next_pattern = ebnf_semantic.Concatenation(terms, terms[0].offset)

		possible_map1 = concatenate_to_map({c: subpattern for c, subpattern in prefix_map.items() if c != None}, terms, ast_info, cache)
		possible_map2 = get_prefix_map(next_pattern, ast_info, cache)
		return merge_maps(possible_map1, possible_map2, ast_info, cache)

	if ebnf_semantic.Identifier in map(type, prefix_map.keys()) or PartialIdentifier in map(type, prefix_map.keys()):
		# There can be only a single transition in this case
		expanded_map, is_optional, is_circular = expand_if_optional(prefix_map.keys()[0], ast_info, cache)

		if is_optional:
			return concatenate_to_map(expanded_map, terms, ast_info, cache)
		elif is_circular:
			return {None: None}
#			expanded_map = {c: subpattern for c, subpattern in expanded_map.items() if c != None}
#			pattern = prefix_map.keys()[0]
#			accum_pattern = PartialIdentifier(pattern.identifier, None, None)

#			if len(terms) == 1:
#				next_map = get_prefix_map(terms[0], ast_info, cache)
#			else:
#				next_map = get_prefix_map(ebnf_semantic.Concatenation(terms, terms[0].offset), ast_info, cache)

#			new_next_map = {}

#			for c, subpattern in next_map.items():
#				if subpattern == None:
#					new_next_map[c] = accum_pattern
#				else:
#					new_next_map[c] = ebnf_semantic.Concatenation([accum_pattern, subpattern], accum_pattern.offset)

#			return merge_maps(expanded_map, new_next_map, ast_info, cache)

	new_map = {}

	for c, subpattern in prefix_map.items():
		if subpattern == None:
			if len(terms) == 1:
				next_pattern = terms[0]
			else:
				next_pattern = ebnf_semantic.Concatenation(terms, terms[0].offset)
		else:
			next_pattern = ebnf_semantic.Concatenation([subpattern] + list(terms), subpattern.offset)

		new_map[c] = next_pattern

	return new_map

def get_prefix_map_for_return_pattern(pattern, ast_info, cache):
	return {None: pattern}

def get_prefix_map_for_partial_identifier(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_terminal(pattern, ast_info, cache):
	c = pattern.terminal[0]
	rest = pattern.terminal[1:]

	if not rest:
		return {c: None}

	return {c: ebnf_semantic.Terminal(rest, pattern.offset + 1)}

def get_prefix_map_for_identifier(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_optional(pattern, ast_info, cache):
	submap = get_prefix_map(pattern.rhs, ast_info, cache)

	new_map = {c: subpattern for c, subpattern in submap.items() if c != None}
	new_map[None] = None

	return new_map

def get_prefix_map_for_repetition(pattern, ast_info, cache):
	submap = get_prefix_map(pattern.rhs, ast_info, cache)

	new_map = {}

	for c, subpattern in submap.items():
		if c == None:
			continue

		if subpattern == None:
			new_map[c] = pattern
		else:
			new_map[c] = ebnf_semantic.Concatenation([subpattern, pattern], subpattern.offset)

	new_map[None] = None

	return new_map

def get_prefix_map_for_concatenation(pattern, ast_info, cache):
	submap = get_prefix_map(pattern.terms[0], ast_info, cache)
	return concatenate_to_map(submap, pattern.terms[1:], ast_info, cache)

def get_prefix_map_for_alternation(pattern, ast_info, cache):
	submaps = [get_prefix_map(subpattern, ast_info, cache) for subpattern in pattern.clauses]
	return reduce(lambda map1, map2: merge_maps(map1, map2, ast_info, cache), submaps)

def get_prefix_map(pattern, ast_info, cache):
	if pattern not in cache["maps"]:
		getters = {ebnf_semantic.Alternation: get_prefix_map_for_alternation,
				ebnf_semantic.Concatenation: get_prefix_map_for_concatenation,
				ebnf_semantic.Repetition: get_prefix_map_for_repetition,
				ebnf_semantic.Optional: get_prefix_map_for_optional,
				ebnf_semantic.Identifier: get_prefix_map_for_identifier,
				ebnf_semantic.Terminal: get_prefix_map_for_terminal,
				PartialIdentifier: get_prefix_map_for_partial_identifier}

		cache["maps"][pattern] = getters[type(pattern)](pattern, ast_info, cache)

	return cache["maps"][pattern]

def build_state_graph_recurse(pattern, ast_info, cache):
	if pattern not in cache["graphs"]:
		nodes = {}
		entry_node = StateNode()
		graph = StateGraph(nodes, entry_node.uid)

		nodes[entry_node.uid] = entry_node
		cache["graphs"][pattern] = graph

		prefix_map = get_prefix_map(pattern, ast_info, cache)

		for c, subpattern in prefix_map.items():
			if subpattern == None:
				entry_node.transitions[c] = None
			else:
				subgraph = build_state_graph_recurse(subpattern, ast_info, cache)
				nodes.update(subgraph.nodes)
				entry_node.transitions[c] = subgraph.entry

	return cache["graphs"][pattern]

def build_state_graph(identifier, ast_info):
	cache = {"graphs": {None: None}, "maps": {}, "partials": {}}
	subgraph = build_state_graph_recurse(ast_info.rules[identifier], ast_info, cache)
	return subgraph, cache

def build_state_graphs(ast_info):
	return {identifier: build_state_graph(identifier, ast_info) for identifier in ["U"]}#ast_info.rules}

if len(sys.argv) != 3:
	print "Usage: %s <grammar file> <top_id>"%(sys.argv[0])
	quit()

filename = sys.argv[1]
top_id = sys.argv[2]

with open(filename, 'r') as f:
	description = f.read()

ast_info = ebnf_semantic.create_ast(description, top_id)

graphs = build_state_graphs(ast_info)

for _, (graph, _) in graphs.items():
	graph.init_labels()

for identifier, (graph, _) in graphs.items():
	print "/* %s */"%repr(ast_info.rules[identifier])
	print "def parse_%s(accumulator=0, state=%s)"%(identifier, graph.labels[graph.entry])
	print "{"
	graph.pretty_print({ident: cache for ident, (_, cache) in graphs.items()}, ast_info)
	print "}"
	print ""