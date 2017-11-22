class InvalidTerminal(object):
	def __init__(self, terminal, error, offset):
		self.terminal = terminal
		self.error = error
		self.offset = offset

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.terminal), repr(self.error))

class Terminal(object):
	def __init__(self, terminal, offset):
		self.terminal = terminal
		self.offset = offset
		self.text = terminal

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.terminal))

class InvalidAlternation(object):
	def __init__(self, errors, offset):
		self.errors = errors
		self.offset = offset

	def __repr__(self):
		return "%s()"%(type(self).__name__)

class InvalidConcatenation(object):
	def __init__(self, contents, error, offset):
		self.contents = contents
		self.error = error
		self.offset = offset

	def __repr__(self):
		return "%s(%s, %s)"%(type(self).__name__, repr(self.contents), repr(self.error))

class InvalidRule(object):
	def __init__(self, identifier, contents, error, offset):
		self.identifier = identifier
		self.contents = contents
		self.error = error
		self.offset = offset

	def __repr__(self):
		return "%s(%s, %s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.contents), repr(self.error))

class EmptyOptional(object):
	def __init__(self, offset):
		self.offset = offset
		self.text = ""

	def __repr__(self):
		return "%s()"%type(self).__name__

class Continue(object):
	pass

class Alternation(object):
	def __init__(self, contents, offset):
		self.contents = contents
		self.offset = offset
		self.text = set([x.text for x in contents]) # XXX WONTWORK

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.contents))

class Concatenation(object):
	def __init__(self, contents, offset):
		self.contents = contents
		self.offset = offset
		self.text = "".join([x.text for x in contents])

	def __repr__(self):
		return "%s(%s)"%(type(self).__name__, repr(self.contents))

class Rule(object):
	def __init__(self, identifier, contents, offset):
		self.identifier = identifier
		self.contents = contents
		self.offset = offset

		if self.contents == None:
			self.text = ""
		elif type(self.contents) in [Rule, Terminal]:
			self.text = contents.text
		else:
			self.text = "".join([x.text for x in contents])

	def __repr__(self):
		if self.identifier in ["identifier", "terminal", "whitespace_sequence"]:
			return "%s(%s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.text))

		return "%s(%s, %s)"%(type(self).__name__, repr(self.identifier), repr(self.contents))

process_counts = 0
class Parser(object):
	def __init__(self, *args):
		self._init(*args)

	def process(self):
		global process_counts
		process_counts += 1
		result = self._process()
		return result

class CharsetParser(Parser):
	def _init(self, text, offset, charset):
		self.text = text
		self.offset = offset
		self.charset = charset

	def _process(self):
		if self.offset >= len(self.text):
			return InvalidAlternation(frozenset([InvalidTerminal(c, "", self.offset) for c in self.charset]), self.offset)

		if self.text[self.offset] not in self.charset:
			return InvalidAlternation(frozenset([InvalidTerminal(c, self.text[self.offset], self.offset) for c in self.charset]), self.offset)

		return Terminal(self.text[self.offset], self.offset)

class TerminalParser(Parser):
	def _init(self, text, offset, terminal):
		self.text = text
		self.offset = offset
		self.terminal = terminal

	def _process(self):
		if self.text[self.offset:].startswith(self.terminal):
			return Terminal(self.terminal, self.offset)

		return InvalidTerminal(self.terminal, self.text[self.offset:], self.offset)

class RuleParser(Parser):
	def _init(self, text, offset, identifier):
		self.identifier = identifier
		self.parser = parser_for_rule(text, offset, identifier)

	def _process(self):
		result = self.parser.process()

		if is_invalid_alternation(result):
			return InvalidRule(self.identifier, None, result, result.offset) # XXX

		if is_invalid_concatenation(result):
			return InvalidRule(self.identifier, result.contents, result.error, result.offset)

		if is_invalid_element(result):
			return InvalidRule(self.identifier, None, result, result.offset)

		if is_empty_optional(result):
			return Rule(self.identifier, None, result.offset)

		if is_continue(result):
			return Continue()

		if is_alternation(result):
			return Rule(self.identifier, result.contents, result.offset)

		if is_concatenation(result):
			return Rule(self.identifier, result.contents, result.offset)

		return Rule(self.identifier, result, result.offset)

class OptionalParser(Parser):
	def _init(self, text, offset, parser_class, *args):
		self.parser = parser_class(text, offset, *args)

	def _process(self):
		result = self.parser.process()

		if is_invalid_alternation(result):
			return EmptyOptional(result.offset)

		if is_invalid_concatenation(result):
			return EmptyOptional(result.offset)

		if is_invalid_element(result):
			return EmptyOptional(result.offset)

		if is_empty_optional(result):
			return EmptyOptional(result.offset)

		if is_continue(result):
			return Continue()

		if len(result.text) == 0:
			return EmptyOptional(result.offset)

		if is_alternation(result):
			return result

		if is_concatenation(result):
			return result

		return result

class RepetitionParser(Parser):
	def _init(self, text, offset, parser_class, *args):
		self.text = text
		self.offset = offset
		self.cur_offset = offset
		self.parser_class = parser_class
		self.args = args
		self.parser = parser_class(text, offset, *args)
		self.repeats = []

	def _process(self):
		result = self.parser.process()

		if is_invalid_alternation(result):
			if not self.repeats:
				return EmptyOptional(self.offset)

			return Concatenation(tuple(self.repeats), self.offset)

		if is_invalid_concatenation(result):
			if not self.repeats:
				return EmptyOptional(self.offset)

			return Concatenation(tuple(self.repeats), self.offset)

		if is_invalid_element(result):
			if not self.repeats:
				return EmptyOptional(self.offset)

			return Concatenation(tuple(self.repeats), self.offset)

		if is_empty_optional(result):
			return Continue()

		if is_continue(result):
			return Continue()

		if is_alternation(result):
			self.repeats.append(result.contents)

			self.cur_offset += len(result.text)
			self.parser = self.parser_class(self.text, self.cur_offset, *self.args)
			return Continue()

		if is_concatenation(result):
			self.repeats.extend(result.contents)

			self.cur_offset += len(result.text)
			self.parser = self.parser_class(self.text, self.cur_offset, *self.args)
			return Continue()

		self.repeats.append(result)

		self.cur_offset += len(result.text)
		self.parser = self.parser_class(self.text, self.cur_offset, *self.args)
		return Continue()

class ConcatenationParser(Parser):
	def _init(self, text, offset, parse_sequence):
		parser_class, args = parse_sequence[0][0], parse_sequence[0][1:]

		self.text = text
		self.offset = offset
		self.cur_offset = offset
		self.parse_sequence = parse_sequence
		self.index = 0
		self.parser = parser_class(text, offset, *args)
		self.concatenation = []

	def _process(self):
		result = self.parser.process()

		if is_invalid_alternation(result):
			return InvalidConcatenation(tuple(self.concatenation), None, self.offset)

		if is_invalid_concatenation(result):
			self.concatenation.extend(result.contents)
			return InvalidConcatenation(tuple(self.concatenation), result.error, self.offset)

		if is_invalid_element(result):
			return InvalidConcatenation(tuple(self.concatenation), result, self.offset)

		if is_continue(result):
			return Continue()

		if is_alternation(result):
			self.concatenation.append(result.contents)
		elif is_concatenation(result):
			self.concatenation.extend(result.contents)
		elif not is_empty_optional(result):
			self.concatenation.append(result)

		self.cur_offset += len(result.text)
		self.index += 1

		if self.index < len(self.parse_sequence):
			parser_class, args = self.parse_sequence[self.index][0], self.parse_sequence[self.index][1:]
			self.parser = parser_class(self.text, self.cur_offset, *args)
			return Continue()

		return Concatenation(tuple(self.concatenation), self.offset)

class AlternationParser(Parser):
	def _init(self, text, offset, parse_set):
		self.offset = offset
		self.parsers = set([parse_tuple[0](text, offset, *parse_tuple[1:]) for parse_tuple in parse_set])
		self.alternatives = set([])
		self.errors = set([])

	def _process(self):
		new_parsers = self.parsers.copy()

		for parser in self.parsers:
			result = parser.process()

			if is_invalid_alternation(result):
				self.errors.add(result)
				new_parsers.remove(parser)
				continue

			if is_invalid_concatenation(result):
				self.errors.add(result)
				new_parsers.remove(parser)
				continue

			if is_invalid_element(result):
				self.errors.add(result)
				new_parsers.remove(parser)
				continue

			if is_empty_optional(result):
				self.alternatives.add(result)
				new_parsers.remove(parser)
				continue

			if is_continue(result):
				continue

			if is_alternation(result):
				self.alternatives.add(result)#XXX
				new_parsers.remove(parser)
				break
				continue

			if is_concatenation(result):
				self.alternatives.add(result)
				new_parsers.remove(parser)
				break
				continue

			new_parsers.remove(parser)
			self.alternatives.add(result)
			break

		self.parsers = new_parsers

		if self.parsers and not self.alternatives:
			return Continue()

		if not self.alternatives:
			return InvalidAlternation(self.errors, self.offset)

		if len(self.alternatives) > 1:
			#return Alternation(frozenset(self.alternatives))
			return self.alternatives.pop()

		return self.alternatives.pop()

def parser_for_rule(text, offset, identifier):
	parser_class, args = ebnf_rules[identifier][0], ebnf_rules[identifier][1:]
	return parser_class(text, offset, *args)

def is_invalid_alternation(result):
	return type(result) == InvalidAlternation

def is_invalid_concatenation(result):
	return type(result) == InvalidConcatenation

def is_invalid_element(result):
	return type(result) in [InvalidRule, InvalidTerminal]

def is_empty_optional(result):
	return type(result) == EmptyOptional

def is_continue(result):
	return type(result) == Continue

def is_alternation(result):
	return type(result) == Alternation

def is_concatenation(result):
	return type(result) == Concatenation

ebnf_letters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
ebnf_digits = "0123456789"
ebnf_symbols = "[]{}()<>+-*/%&|^=#@_~`:;?.,!"
ebnf_whitespaces = " \t\n"
ebnf_escape_codes = "nt\\'\""

ebnf_rules = {}
ebnf_rules["letter"] = (CharsetParser, frozenset(ebnf_letters))
ebnf_rules["digit"] = (CharsetParser, frozenset(ebnf_digits))
ebnf_rules["symbol"] = (CharsetParser, frozenset(ebnf_symbols))
ebnf_rules["whitespace"] = (CharsetParser, frozenset(ebnf_whitespaces))
ebnf_rules["whitespace_sequence"] = (RepetitionParser, RuleParser, "whitespace")
ebnf_rules["escape_code"] = (CharsetParser, frozenset(ebnf_escape_codes))
ebnf_rules["escape_sequence"] = (ConcatenationParser, ((TerminalParser, "\\"), (RuleParser, "escape_code")))
ebnf_rules["character"] = (AlternationParser, frozenset([(RuleParser, "letter"), (RuleParser, "digit"), (RuleParser, "symbol"), (RuleParser, "whitespace"), (RuleParser, "escape_sequence")]))
ebnf_rules["character1"] = (AlternationParser, frozenset([(TerminalParser, '"'), (RuleParser, "character")]))
ebnf_rules["character2"] = (AlternationParser, frozenset([(TerminalParser, "'"), (RuleParser, "character")]))
ebnf_rules["identifier"] = (ConcatenationParser, ((RuleParser, "letter"), (RepetitionParser, AlternationParser, frozenset([(RuleParser, "letter"), (RuleParser, "digit"), (TerminalParser, "_")]))))
ebnf_rules["terminal"] = (AlternationParser, frozenset([(ConcatenationParser, ((TerminalParser, "'"), (RuleParser, "character1"), (RepetitionParser, RuleParser, "character1"), (TerminalParser, "'"))),
	(ConcatenationParser, ((TerminalParser, '"'), (RuleParser, "character2"), (RepetitionParser, RuleParser, "character2"), (TerminalParser, '"')))]))
ebnf_rules["lhs"] = (ConcatenationParser, ((OptionalParser, RuleParser, "whitespace_sequence"), (RuleParser, "identifier"), (OptionalParser, RuleParser, "whitespace_sequence")))
ebnf_rules["term"] = (AlternationParser, frozenset([(RuleParser, "identifier"), (RuleParser, "terminal"),
	(ConcatenationParser, ((TerminalParser, "["), (RuleParser, "rhs"), (TerminalParser, "]"))),
	(ConcatenationParser, ((TerminalParser, "{"), (RuleParser, "rhs"), (TerminalParser, "}"))),
	(ConcatenationParser, ((TerminalParser, "("), (RuleParser, "rhs"), (TerminalParser, ")")))]))
ebnf_rules["spaced_term"] = (ConcatenationParser, ((OptionalParser, RuleParser, "whitespace_sequence"), (RuleParser, "term"), (OptionalParser, RuleParser, "whitespace_sequence")))
ebnf_rules["clause"] = (ConcatenationParser, ((RuleParser, "spaced_term"), (RepetitionParser, ConcatenationParser, ((TerminalParser, ","), (RuleParser, "spaced_term")))))
ebnf_rules["rhs"] = (ConcatenationParser, ((RuleParser, "clause"), (RepetitionParser, ConcatenationParser, ((TerminalParser, "|"), (RuleParser, "clause")))))
ebnf_rules["rule"] = (ConcatenationParser, ((RuleParser, "lhs"), (TerminalParser, "="), (RuleParser, "rhs"), (TerminalParser, ";")))
ebnf_rules["grammar"] = (ConcatenationParser, ((RepetitionParser, RuleParser, "rule"), (OptionalParser, RuleParser, "whitespace_sequence")))

def parse(description):
	parser = RuleParser(description, 0, "grammar")
	result = Continue()
	list_process_counts = []

	while is_continue(result):
		global process_counts
		process_counts = 0
		result = parser.process()
		list_process_counts.append(process_counts)

	if len(result.text) < len(description):
		parser = RuleParser(description, len(result.text), "rule")
		result = Continue()

		while is_continue(result):
			result = parser.process()

		return result

	return result
