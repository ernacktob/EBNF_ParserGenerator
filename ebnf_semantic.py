import ebnf_syntax

class AST_Info(object):
	def __init__(self, top_id, rules, offsets, text):
		self._top_id = top_id
		self._rules = rules
		self._offsets = offsets
		self._text = text

	def __repr__(self):
		return "%s(%s, %s, %s, %s)"%(type(self).__name__, repr(self.top_id), repr(self.rules), repr(self.offsets), repr(self.text))

	@property
	def top_id(self):
		return self._top_id

	@property
	def rules(self):
		return self._rules

	@property
	def offsets(self):
		return self._offsets

	@property
	def text(self):
		return self._text

class EBNF_Pattern(object):
	def __hash__(self):
		return hash(repr(self))

	def __eq__(self, other):
		return repr(self) == repr(other)

class Terminal(EBNF_Pattern):
	def __init__(self, terminal, offset):
		self._terminal = terminal
		self._offset = offset

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.terminal))

	@property
	def terminal(self):
		return self._terminal

	@property
	def offset(self):
		return self._offset

class Identifier(EBNF_Pattern):
	def __init__(self, identifier, offset):
		self._identifier = identifier
		self._offset = offset

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.identifier))

	@property
	def identifier(self):
		return self._identifier

	@property
	def offset(self):
		return self._offset

class Optional(EBNF_Pattern):
	def __init__(self, rhs, offset):
		self._rhs = rhs
		self._offset = offset

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.rhs))

	@property
	def rhs(self):
		return self._rhs

	@property
	def offset(self):
		return self._offset

class Repetition(EBNF_Pattern):
	def __init__(self, rhs, offset):
		self._rhs = rhs
		self._offset = offset

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.rhs))

	@property
	def rhs(self):
		return self._rhs

	@property
	def offset(self):
		return self._offset

class Concatenation(EBNF_Pattern):
	def __init__(self, terms, offset):
		self._terms = tuple(terms)
		self._offset = offset

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.terms))

	@property
	def terms(self):
		return self._terms

	@property
	def offset(self):
		return self._offset

class Alternation(EBNF_Pattern):
	def __init__(self, clauses, offset):
		self._clauses = tuple(clauses)
		self._offset = offset

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.clauses))

	@property
	def clauses(self):
		return self._clauses

	@property
	def offset(self):
		return self._offset

def get_line_col(text, offset):
	len_so_far = 0
	prev_len_so_far = 0

	for i, line in enumerate(text.split("\n")):
		prev_len_so_far = len_so_far
		len_so_far += len(line) + 1

		if len_so_far > offset:
			break

	linenum = i + 1
	colnum = offset - prev_len_so_far + 1

	return linenum, colnum

def print_error(text, grammar):
	thing = grammar.error

	while type(thing) == ebnf_syntax.InvalidRule:
		thing = thing.error

	linenum, colnum = get_line_col(text, thing.offset)

	print "EBNF error at line %d, column %d"%(linenum, colnum)
	print thing

def get_identifier(lhs):
	if lhs.contents[0].identifier == "identifier":
		return lhs.contents[0].text, lhs.contents[0].offset

	return lhs.contents[1].text, lhs.contents[1].offset

def unescape_character(escaped_char):
	unescapes = {"n": "\n", "t": "\t", "\\": "\\", "'": "'", '"': '"'}
	code = escaped_char.contents[1].text

	return unescapes[code]

def get_character(character12):
	if type(character12.contents) == ebnf_syntax.Rule:
		character = character12.contents

		if character.contents.identifier == "escape_sequence":
			return unescape_character(character.contents)

		return character.text

	return character12.text

def get_terminal(terminal):
	result = ""

	for element in terminal.contents[1:-1]:
		character = get_character(element)
		result += character

	return result

def get_term(spaced_term):
	if spaced_term.contents[0].identifier == "term":
		term = spaced_term.contents[0]
	else:
		term = spaced_term.contents[1]

	if type(term.contents) == ebnf_syntax.Rule and term.contents.identifier == "identifier":
		return Identifier(term.contents.text, term.offset)
	elif type(term.contents) == ebnf_syntax.Rule and term.contents.identifier == "terminal":
		terminal = get_terminal(term.contents)
		return Terminal(terminal, term.offset)
	elif term.contents[0].text == "[":
		rhs = get_rhs(term.contents[1])
		return Optional(rhs, term.offset)
	elif term.contents[0].text == "{":
		rhs = get_rhs(term.contents[1])
		return Repetition(rhs, term.offset)
	else:
		# Group "(...)" is just a passthrough
		rhs = get_rhs(term.contents[1])
		return rhs

def get_clause(clause):
	terms = []

	for element in clause.contents:
		if type(element) == ebnf_syntax.Rule and element.identifier == "spaced_term":
			term = get_term(element)
			terms.append(term)

	if len(terms) == 1:
		return terms[0]

	return Concatenation(terms, terms[0].offset)

def get_rhs(rhs):
	clauses = []
	offset = None

	for element in rhs.contents:
		if type(element) == ebnf_syntax.Rule and element.identifier == "clause":
			clause = get_clause(element)
			clauses.append(clause)

			if offset == None or clause.offset < offset:
				offset = clause.offset

	if len(clauses) == 1:
		return clauses[0]

	return Alternation(clauses, offset)

def get_rule(rule):
	lhs = rule.contents[0]
	rhs = rule.contents[2]

	identifier, offset = get_identifier(lhs)
	rhs = get_rhs(rhs)

	return identifier, offset, rhs

def get_rules(grammar, top_id):
	rules = {}
	offsets = {}

	for element in grammar.contents:
		if type(element) == ebnf_syntax.Rule and element.identifier == "rule":
			identifier, offset, rhs = get_rule(element)

			if identifier in rules:
				linenumA, colnumA = get_line_col(grammar.text, offsets[identifier])
				linenumB, colnumB = get_line_col(grammar.text, offset)

				if offsets[identifier] < offset:
					linenum1 = linenumA
					linenum2 = linenumB
					colnum1 = colnumA
					colnum2 = colnumB
				else:
					linenum1 = linenumB
					linenum2 = linenumA
					colnum1 = colnumB
					colnum2 = colnumA

				print "Duplicate definition of rule %s at line %d, column %d (previous definition at line %d, column %d)."%(repr(identifier), linenum2, colnum2, linenum1, colnum1)
				quit()

			rules[identifier] = rhs
			offsets[identifier] = offset

	return AST_Info(top_id, rules, offsets, grammar.text)

def create_ast(description, top_id):
	grammar = ebnf_syntax.parse(description)

	if type(grammar) == ebnf_syntax.InvalidRule:
		print_error(description, grammar)
		quit()

	ast_info = get_rules(grammar, top_id)

	return ast_info
