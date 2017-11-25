import sys

import ebnf_semantic

def kaka():
	if ebnf_semantic.Identifier in map(type, self.transitions.keys()):
		for c, next_state in self.transitions.items():
			if c == None:
				continue

			print "\tif (parse_%s())"%c.identifier
			print "\t\tgoto state_%s;"%labels[next_state]

		print "\telse"
		print "\t\tgoto state_error;"
		print ""
	elif PartialIdentifier in map(type, self.transitions.keys()):
		for c, next_state in self.transitions.items():
			if c == None:
				continue

			if c.subpattern == None:
				print "\tif (parse_%s(%d, state_success))"%(c.identifier, c.accumulator)
				print "\t\tgoto state_%s;"%labels[next_state]
			else:
				subpat_graph = caches[c.identifier]["graphs"][c.subpattern]
				ident_graph = caches[c.identifier]["graphs"][ast_info.rules[c.identifier]]

				print "\tif (parse_%s(%d, state_%s))"%(c.identifier, c.accumulator, ident_graph.labels[subpat_graph.entry])
				print "\t\tgoto state_%s;"%labels[next_state]

		print "\telse"
		print "\t\tgoto state_error;"
		print ""
	elif str not in map(type, self.transitions.keys()):
		for c, next_state in self.transitions.items():
			if c == None:
				continue

			print "\tif (parse(%s))"%c
			print "\t\tgoto state_%s;"%labels[next_state]

		print "\telse"
		print "\t\tgoto state_error;"
		print ""
	else:
		pass

def custom_repr(c):
	if c == "'":
		return "\'\\\'\'"

	return repr(c)

def print_parser_for_reduce_action(pattern, identifier, prefix, success_label, ast_info, caches):
	pass

def print_parser_for_partial_identifier(pattern, identifier, prefix, success_label, ast_info, caches):
	pass

def print_parser_for_terminal(pattern, identifier, indent, prefix, next_label, ast_info, optional, caches):
	if optional:
		print indent + "\tif (!strparse(%s)) {"%repr(pattern.terminal)
		print indent + "\t\tbacktrack();"
		print indent + "\t\tbreak;"
		print indent + "\t}"
	else:
		print indent + "\tif (strparse(%s))"%repr(pattern.terminal)
		print indent + "\t\tgoto %s;"%next_label
		print indent + "\telse"
		print indent + "\t\tgoto state_error;"
		print ""

def print_parser_for_identifier(pattern, identifier, indent, prefix, next_label, optional, ast_info, caches):
	if optional:
		print indent + "\tif (!parse_%s()) {"%pattern.identifier
		print indent + "\t\tbacktrack();"
		print indent + "\t\tbreak;"
		print indent + "\t}"
	else:
		print indent + "\tif (parse_%s())"%pattern.identifier
		print indent + "\t\tgoto %s;"%next_label
		print indent + "\telse"
		print indent + "\t\tgoto state_error;"
		print ""

def print_parser_for_optional(pattern, identifier, indent, prefix, next_label, optional, ast_info, caches):
	subgraph = build_state_graph_recurse(pattern.rhs, ast_info, caches[identifier])
	subgraph.init_labels(identifier, indent + "\t", prefix, next_label, optional=True)

	print indent + "\twhile (1) {"
	subgraph.pretty_print(ast_info, caches)
	print ""
	print indent + "\t\tbreak;"
	print indent + "\t}"
	print ""
	print indent + "\tgoto %s;"%next_label
	print ""

def print_parser_for_repetition(pattern, identifier, indent, prefix, next_label, optional, ast_info, caches):
	subgraph = build_state_graph_recurse(pattern.rhs, ast_info, caches[identifier])
	subgraph.init_labels(identifier, indent + "\t", prefix, next_label, optional=True)

	print indent + "\twhile (1) {"
	subgraph.pretty_print(ast_info, caches)
	print indent + "\t}"
	print ""
	print indent + "\tgoto %s;"%next_label
	print ""

def print_parser_for_pattern(pattern, identifier, indent, prefix, next_label, optional, ast_info, caches):
	printers = {ebnf_semantic.Repetition: print_parser_for_repetition,
			ebnf_semantic.Optional: print_parser_for_optional,
			ebnf_semantic.Identifier: print_parser_for_identifier,
			ebnf_semantic.Terminal: print_parser_for_terminal,
			PartialIdentifier: print_parser_for_partial_identifier,
			ReduceAction: print_parser_for_reduce_action}

	printers[type(pattern)](pattern, identifier, indent, prefix, next_label, optional, ast_info, caches)

class StateNode(object):
	def __init__(self):
		self.uid = id(self)
		self.transitions = {}

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.uid), repr(self.transitions))

	def pretty_print(self, labels, identifier, indent, prefix, optional, ast_info, caches):
		transitions = {c: next_state for c, next_state in self.transitions.items() if c != None}

		print indent + "%s:"%(prefix + labels[self.uid])

		if len(transitions) > 1:
			print indent + "\tif (EOF())"

			if None in self.transitions:
				print indent + "\t\tgoto %s;\n"%(prefix + labels[self.transitions[None]])
			else:
				print indent + "\t\tgoto state_error;\n"

			print indent + "\tswitch (c) {"

			for c, next_state in transitions.items():
				print indent + "\t\tcase %s:"%custom_repr(c)
				print indent + "\t\t\tgoto %s;"%(prefix + labels[next_state])

			print indent + "\t\tdefault:"

			if None in self.transitions:
				print indent + "\t\t\tbacktrack();"
				print indent + "\t\t\tgoto %s;"%(prefix + labels[self.transitions[None]])
			else:
				print indent + "\t\t\tgoto state_error;"

			print indent + "\t}\n"
		else:
			pattern = transitions.keys()[0]
			next_label = labels[transitions[pattern]]
			print_parser_for_pattern(pattern, identifier, indent, prefix + labels[self.uid] + "_", prefix + next_label, optional, ast_info, caches)

class StateGraph(object):
	def __init__(self, nodes, entry):
		self.nodes = nodes
		self.entry = entry
		self.labels = {}
		self.identifier = None
		self.indent = None
		self.prefix = None
		self.is_optional = None
		self.is_top_level = None
		self.inited = False

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.nodes), repr(self.entry))

	def init_labels(self, identifier, indent="", prefix="state_", next_label=None, optional=False):
		if not self.inited:
			for i, state in enumerate(self.nodes):
				self.labels[state] = str(i)

			if next_label:
				self.labels[None] = next_label
				self.is_top_level = False
			else:
				self.labels[None] = "success"
				self.is_top_level = True

			self.identifier = identifier
			self.indent = indent
			self.prefix = prefix
			self.optional = optional
			self.inited = True

	def pretty_print(self, ast_info, caches):
		if self.is_top_level:
			print self.indent + "\tgoto %s;\n"%(self.prefix + self.labels[self.entry])

		for state in self.nodes:
			self.nodes[state].pretty_print(self.labels, self.identifier, self.indent, self.prefix, self.optional, ast_info, caches)

		# Only on top-level graph
		if self.is_top_level:
			print "state_success:"
			print "\tsuccess();"
			print ""
			print "state_error:"
			print "\terror();"

class PartialIdentifier(ebnf_semantic.EBNF_Pattern):
	def __init__(self, identifier, accumulator, subpattern):
		self.identifier = identifier
		self.accumulator = accumulator
		self.subpattern = subpattern
		self.offset = subpattern.offset

	def __repr__(self):
		return "%s(%s, %s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.accumulator), repr(self.subpattern))

class ReduceAction(ebnf_semantic.EBNF_Pattern):
	def __init__(self, identifier, length, delay):
		self.identifier = identifier
		self.length = length
		self.delay = delay
		self.offset = 0

	def __repr__(self):
		return "%s(%s, %s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.length), repr(self.delay))

def delay_reduce_action(pattern):
	return ReduceAction(pattern.identifier, pattern.length, pattern.delay + 1)

def expand_reduce_action(pattern, ast_info, cache):
	return {None: pattern}

def expand_partial_identifier(pattern, ast_info, cache):
	submap = get_prefix_map(pattern.subpattern, ast_info, cache)

	new_map = {}

	for c, subpattern in submap.items():
		if c == None:
			if subpattern == None:
				new_map[c] = ReduceAction(pattern.identifier, pattern.accumulator, 0)
			else:
				new_map[c] = PartialIdentifier(pattern.identifier, pattern.accumulator, subpattern)
		else:
			if subpattern == None:
				new_map[c] = ReduceAction(pattern.identifier, pattern.accumulator + 1, 0)
			else:
				new_map[c] = PartialIdentifier(pattern.identifier, pattern.accumulator + 1, subpattern)

	return new_map

def expand_terminal(pattern, ast_info, cache):
	c = pattern.terminal[0]
	rest = pattern.terminal[1:]

	if rest:
		return {ebnf_semantic.Terminal(c, pattern.offset): ebnf_semantic.Terminal(rest, pattern.offset + 1)}

	return {ebnf_semantic.Terminal(c, pattern.offset): None}

def expand_identifier(pattern, ast_info, cache):
	submap = get_prefix_map(ast_info.rules[pattern.identifier], ast_info, cache)
	new_map = {}

	for c, subpattern in submap.items():
		if c == None:
			if subpattern == None:
				new_map[c] = ReduceAction(pattern.identifier, 0, 0)
			else:
				new_map[c] = PartialIdentifier(pattern.identifier, 0, subpattern)
		else:
			if subpattern == None:
				new_map[c] = ReduceAction(pattern.identifier, 1, 0)
			else:
				new_map[c] = PartialIdentifier(pattern.identifier, 1, subpattern)

	return new_map

def expand_optional(pattern, ast_info, cache):
	submap = get_prefix_map(pattern.rhs, ast_info, cache)

	new_map = {c: subpattern for c, subpattern in submap.items() if c != None}
	new_map[None] = None

	return new_map

def expand_repetition(pattern, ast_info, cache):
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

def expand_pattern(pattern, ast_info, cache):
	if pattern not in cache["expansions"]:
		expanders = {ebnf_semantic.Repetition: expand_repetition,
				ebnf_semantic.Optional: expand_optional,
				ebnf_semantic.Identifier: expand_identifier,
				ebnf_semantic.Terminal: expand_terminal,
				PartialIdentifier: expand_partial_identifier,
				ReduceAction: expand_reduce_action}

		cache["expansions"][pattern] = expanders[type(pattern)](pattern, ast_info, cache)

	return cache["expansions"][pattern]

def expand_term(term, ast_info, cache):
	prefix_map1 = expand_pattern(term, ast_info, cache)
	prefix_map = {}

	for c, subpattern in prefix_map1.items():
		if type(c) == str:
			prefix_map[ebnf_semantic.Terminal(c)] = subpattern
		else:
			prefix_map[c] = subpattern

	clauses = []

	for pattern, next_pattern in prefix_map.items():
		clauses.append(simplify_list(ebnf_semantic.Concatenation([pattern, next_pattern])))

	return simplify_list(ebnf_semantic.Alternation(clauses))

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

def simplify_concatenation_to_optional(term1, term2):
	clause1 = simplify_list(ebnf_semantic.Concatenation([term1.rhs, term2]))
	return simplify_list(ebnf_semantic.Alternation([clause1, term2]))

def simplify_concatenation_to_repetition(term1, term2):
	term1 = ebnf_semantic.Optional(simplify_list(ebnf_semantic.Concatenation([term1.rhs, term1])))
	return simplify_concatenation_to_optional(term1, term2)

def simplify_alternation_with_optional(pattern):
	clauses = [clause.rhs if type(clause) == ebnf_semantic.Optional else clause for clause in pattern.clauses]
	return ebnf_semantic.Optional(simplify_list(ebnf_semantic.Alternation(clauses)))

def simplify_alternation_with_repetition(pattern):
	clauses = [simplify_list(ebnf_semantic.Concatenation([clause.rhs, clause])) if type(clause) == ebnf_semantic.Repetition else clause for clause in pattern.clauses]
	return ebnf_semantic.Optional(simplify_list(ebnf_semantic.Alternation(clauses)))

def simplify_alternation_with_common_prefixes(pattern):
	threads = {}
	simplified = False

	for clause in pattern.clauses:
		if type(clause) == ebnf_semantic.Concatenation:
			first_term = clause.terms[0]
			next_pattern = simplify_list(ebnf_semantic.Concatenation(clause.terms[1:]))
		else:
			first_term = clause
			next_pattern = None

		if first_term not in threads:
			threads[first_term] = []

		threads[first_term].append(next_pattern)

	for term, clauses in threads.items():
		if len(clauses) > 1:
			simplified = True

		threads[term] = simplify_list(ebnf_semantic.Alternation(clauses))

	if not simplified:
		return pattern, False, threads

	clauses = []

	for pattern, next_pattern in threads.items():
		clause = simplify_list(ebnf_semantic.Concatenation([pattern, next_pattern]))
		clauses.append(clause)

	return simplify_list(ebnf_semantic.Alternation(clauses)), simplified, None

def simplify_optionals_in_threads(threads):
	clauses = []

	for pattern, next_pattern in threads.items():
		if type(pattern) == ebnf_semantic.Optional:
			clauses.append(simplify_concatenation_to_optional(pattern, next_pattern))
		else:
			clauses.append(simplify_list(ebnf_semantic.Concatenation([pattern, next_pattern])))

	return simplify_list(ebnf_semantic.Alternation(clauses))

def simplify_repetitions_in_threads(threads):
	clauses = []

	for pattern, next_pattern in threads.items():
		if type(pattern) == ebnf_semantic.Repetition:
			clauses.append(simplify_concatenation_to_repetition(pattern, next_pattern))
		else:
			clauses.append(simplify_list(ebnf_semantic.Concatenation([pattern, next_pattern])))

	return simplify_list(ebnf_semantic.Alternation(clauses))

def simplify_alternations_in_threads(threads):
	clauses = []

	for pattern, next_pattern in threads.items():
		if type(pattern) == ebnf_semantic.Alternation:
			clauses.extend([simplify_list(ebnf_semantic.Concatenation([clause, next_pattern])) for clause in pattern.clauses])
		else:
			clauses.append(simplify_list(ebnf_semantic.Concatenation([pattern, next_pattern])))

	return simplify_list(ebnf_semantic.Alternation(clauses))

def simplify_reduce_actions_in_threads(threads):
	import pdb
	pdb.set_trace()
	clauses = []
	none_actions = []

	for pattern, next_pattern in threads.items():
		if type(pattern) == ReduceAction:
			if next_pattern == None:
				none_actions.append(tuple([pattern]))
			elif type(next_pattern) == ReduceAction:
				none_actions.append(tuple([pattern, next_pattern]))
			elif type(next_pattern) == ebnf_semantic.Concatenation:

			else:
				clauses.append(simplify_list(ebnf_semantic.Concatenation([next_pattern, delay_reduce_action(pattern)])))
		else:
			clauses.append(simplify_list(ebnf_semantic.Concatenation([pattern, next_pattern])))

	none_actions = set(tuple(none_actions))
	return simplify_list(ebnf_semantic.Alternation(clauses)), none_actions

def get_prefix_map_for_reduce_action(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_partial_identifier(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_terminal(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_identifier(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_optional(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_repetition(pattern, ast_info, cache):
	return {pattern: None}

def get_prefix_map_for_concatenation(pattern, ast_info, cache):
	if len(pattern.terms) > 2:
		next_pattern = ebnf_semantic.Concatenation(pattern.terms[1:])
	else:
		next_pattern = pattern.terms[1]

	if type(pattern.terms[0]) == ebnf_semantic.Optional:
		return get_prefix_map(simplify_concatenation_to_optional(pattern.terms[0], next_pattern), ast_info, cache)

	if type(pattern.terms[0]) == ebnf_semantic.Repetition:
		return get_prefix_map(simplify_concatenation_to_repetition(pattern.terms[0], next_pattern), ast_info, cache)

	prefix_map = get_prefix_map(pattern.terms[0], ast_info, cache)
	new_map = {}

	for c, subpattern in prefix_map.items():
		if subpattern != None:
			next_pattern = ebnf_semantic.Concatenation([subpattern, next_pattern])

		new_map[c] = next_pattern

	return new_map

def get_prefix_map_for_alternation(pattern, ast_info, cache):
	pattern1 = simplify_list(pattern)

	if pattern1 != pattern:
		return get_prefix_map(pattern1, ast_info, cache)

	clauses = pattern.clauses

	if ebnf_semantic.Optional in map(type, clauses):
		return get_prefix_map(simplify_alternation_with_optional(pattern), ast_info, cache)

	if ebnf_semantic.Repetition in map(type, clauses):
		return get_prefix_map(simplify_alternation_with_repetition(pattern), ast_info, cache)

	pattern, simplified, threads = simplify_alternation_with_common_prefixes(pattern)

	if simplified:
		return get_prefix_map(pattern, ast_info, cache)

	types = set(map(type, threads.keys()))

	if ebnf_semantic.Optional in types:
		return get_prefix_map(simplify_optionals_in_threads(threads), ast_info, cache)

	if ebnf_semantic.Repetition in types:
		return get_prefix_map(simplify_repetitions_in_threads(threads), ast_info, cache)

	if ebnf_semantic.Alternation in types:
		return get_prefix_map(simplify_alternations_in_threads(threads), ast_info, cache)

	if ReduceAction in types:
		reduced_pattern, none_actions = simplify_reduce_actions_in_threads(threads)
		prefix_map = get_prefix_map(reduced_pattern, ast_info, cache)

		if none_actions:
			if None in prefix_map:
				prefix_map[None] = none_actions | prefix_map[None]
			else:
				prefix_map[None] = none_actions

		return prefix_map

	if types != set([ebnf_semantic.Terminal]) or set(map(lambda x: len(x.terminal), threads.keys())) != set([1]):
		clauses = []

		for term, next_pattern in threads.items():
			expanded_term = expand_term(term, ast_info, cache)
			clauses.append(simplify_list(ebnf_semantic.Concatenation([expanded_term, next_pattern])))

		return get_prefix_map(simplify_list(ebnf_semantic.Alternation(clauses)), ast_info, cache)

	prefix_map = {x.terminal: subpattern for x, subpattern in threads.items()}
	return prefix_map

def get_prefix_map(pattern, ast_info, cache):
	if pattern not in cache["maps"]:
		getters = {ebnf_semantic.Alternation: get_prefix_map_for_alternation,
				ebnf_semantic.Concatenation: get_prefix_map_for_concatenation,
				ebnf_semantic.Repetition: get_prefix_map_for_repetition,
				ebnf_semantic.Optional: get_prefix_map_for_optional,
				ebnf_semantic.Identifier: get_prefix_map_for_identifier,
				ebnf_semantic.Terminal: get_prefix_map_for_terminal,
				PartialIdentifier: get_prefix_map_for_partial_identifier,
				ReduceAction: get_prefix_map_for_reduce_action}

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
	print identifier
	cache = {"graphs": {}, "maps": {}, "expansions": {}}
	subgraph = build_state_graph_recurse(ast_info.rules[identifier], ast_info, cache)
	return subgraph, cache

def build_state_graphs(ast_info):
	return {identifier: build_state_graph(identifier, ast_info) for identifier in ["grammar"]}#ast_info.rules}# if identifier not in ["U"]}

if len(sys.argv) != 3:
	print "Usage: %s <grammar file> <top_id>"%(sys.argv[0])
	quit()

filename = sys.argv[1]
top_id = sys.argv[2]

with open(filename, 'r') as f:
	description = f.read()

ast_info = ebnf_semantic.create_ast(description, top_id)

graphs = build_state_graphs(ast_info)

for identifier, (graph, _) in graphs.items():
	graph.init_labels(identifier)

for identifier, (graph, _) in graphs.items():
	print "/* %s */"%repr(ast_info.rules[identifier])
	print "def parse_%s(accumulator=0, state=%s)"%(identifier, graph.labels[graph.entry])
	print "{"
	graph.pretty_print(ast_info, {ident: cache for ident, (_, cache) in graphs.items()})
	print "}"
	print ""
