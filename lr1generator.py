class Production(object):
    def __init__(self, lhs, rhs):
        self.lhs = str(lhs)
        self.rhs = list(rhs)
        self.item_index = 0

    def __str__(self):
        return '{0} -> {1}'.format(self.lhs, ' '.join(self.rhs))

    def __repr__(self):
        return str(self)
    
    def __eq__(self, other):
        return self.lhs == other.lhs and self.rhs == other.rhs and \
               self.item_index == other.item_index

    def __hash__(self):
        return sum(ord(ch) for ch in self.lhs) + sum(ord(ch) for s in self.rhs
                                                     for ch in s)

class Item(object):
    def __init__(self, production, item_index = 0, follow_set = None):
        self.item_index = item_index
        self.production = production

        if follow_set == None:
            self.follow_set = set()
        else:
            self.follow_set = set(follow_set)

    def __str__(self):
        return '{0} -> {1}~{2} ({3})'.format(self.production.lhs,
                                           ' '.join(self.production.rhs[:self.item_index]),
                                           ' '.join(self.production.rhs[self.item_index:]),
                                           '/'.join(tok for tok in self.follow_set))

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.production == other.production and \
               self.item_index == other.item_index and \
               self.follow_set == other.follow_set

    def __hash__(self):
        return hash(self.production)

    def can_reduce(self):
        return self.item_index == len(self.production.rhs)

    def next_symbol(self):
        return self.production.rhs[self.item_index]

    def copy_and_increment(self):
        if self.can_reduce():
            raise ValueError("Can't increment item index, production reducable")
        return Item(self.production, self.item_index + 1, self.follow_set)


def is_token(ch):
    return not ch.isupper()

def is_nonterminal(ch):
    return ch.isupper()

def is_nullable(nonterminal):
    return nonterminal in nullables
    

def generate_nullable_set(productions):
    nullables = set()
    change = True
    changed_productions = productions

    while change:
        change = False

        new_nullables = {p.lhs for p in changed_productions if len(p.rhs) == 0}
        if len(new_nullables) > len(nullables):
            change = True

        changed_productions = [Production(p.lhs,  [sym for sym in p.rhs if
                                                   not sym in new_nullables]) for
                               p in changed_productions]
        nullables = new_nullables

    return nullables

def build_item_set(start_item, nonterminals_seen = None):
    if nonterminals_seen is None:
        nonterminals_seen = set()
    
    items = set()
    
    # P -> b~A then add all A's productions
    if not start_item.can_reduce():
        next_symbol = start_item.next_symbol()

        if is_nonterminal(next_symbol) and not next_symbol in nonterminals_seen:
            nonterminals_seen.add(next_symbol)
            items = [build_item_set(Item(p), nonterminals_seen) for p in productions if
                     next_symbol == p.lhs]

    items = set.union({start_item}, *items)
    return items

def construct_first_set(symbol_list, nonterminals_seen = None):
    if nonterminals_seen == None:
        nonterminals_seen = set()

    if len(symbol_list) == 0:
        return {""}
    
    first_set = set()
    symbol = symbol_list[0]

    if is_token(symbol):
        # First(aBC) = a
        first_set.add(symbol)
    elif not symbol in nonterminals_seen:
        first_productions = {p for p in productions if p.lhs == symbol and
                             len(p.rhs) > 0}

        # if B -> a... then add a to First(B)
        first_set = first_set.union({p.rhs[0] for p in first_productions if
                                     is_token(p.rhs[0])})

        # if B -> A... then add First(A...) to First(B)
        for p in first_productions:
            first_set = first_set.union(construct_first_set(
                p.rhs, nonterminals_seen.union({symbol})))         

    # if looking for First(BC...) and First(B) contains lambda add First(C...)
    if is_nullable(symbol):
        first_set = first_set.union(construct_first_set(symbol_list[1:], nonterminals_seen))
        
    return first_set

def construct_nonterminal_follow(item_set, nonterminal, nonterminals_seen = None):
    if nonterminals_seen == None:
        nonterminals_seen = set()
        
    follow_set = set()
    for item in item_set:
        # Looking at follow(A) if B->~ACD need to find first(CD)
        if not item.can_reduce() and item.next_symbol() == nonterminal:
            follow_seq = item.production.rhs[item.item_index + 1:]
            follow_set = follow_set.union(construct_first_set(follow_seq))

            # B -> a~ACD and CD can be lambda, need to look at follow(B)
            if "" in follow_set:
                follow_set.remove("")

                follow_set = follow_set.union(*(item_follow.follow_set for item_follow
                                                in item_set if item_follow.production.lhs
                                                == item.production.lhs))

                if not item.production.lhs in nonterminals_seen:
                    follow_set = follow_set.union(construct_nonterminal_follow(
                        item_set, item.production.lhs,
                        nonterminals_seen.union({item.production.lhs})))

    return follow_set

def construct_item_set_follow(item_set):
    for nonterminal in set(item.production.lhs for item in item_set):
        follow = construct_nonterminal_follow(item_set, nonterminal)

        for item in item_set:
            if item.production.lhs == nonterminal:
                item.follow_set = item.follow_set.union(follow)


def build_item_sets(start_item_set):
    next_symbols = {item.next_symbol() for item in start_item_set if
                    not item.can_reduce()}

    transitions = list()
    
    # P -> ~A a, new set P -> A ~a
    for symbol in next_symbols:
        
        new_set = set.union(*map(build_item_set, (item.copy_and_increment() for item in start_item_set if
             not item.can_reduce() and item.next_symbol() == symbol)))

        construct_item_set_follow(new_set)

        try:
            # See which item set transition goes to
            index = item_sets.index(new_set)
            transitions.append((start_item_set, symbol, index))
            
        except ValueError:
            # Do this because list.index throws an exception if item not found
            item_sets.append(new_set)
            transitions.append((start_item_set, symbol, len(item_sets) - 1))
            transitions.extend(build_item_sets(new_set))

    return transitions

def build_parse_table(prods):
    global productions, nullables, item_sets, transitions
    productions = prods
    
    tokens = list({sym for p in productions for sym in p.rhs
                   if is_token(sym)})
    nonterminals = list({sym for p in productions for sym in p.rhs
                         if is_nonterminal(sym)})

    nullables = generate_nullable_set(productions)
    
    item_set_0 = build_item_set(Item(productions[0], follow_set={"$"}))

    construct_item_set_follow(item_set_0)
    
    item_sets = [item_set_0]
    transitions = build_item_sets(item_set_0)

    table = list()
    
    for i, item_set in enumerate(item_sets):
        item_transitions = [transition for transition in transitions if
                       transition[0] == item_set]
        reductions = [item for item in item_set if item.can_reduce()]

        event_dict = dict()

        for token in tokens:
            events = ["S" + str(transition[2]) for transition in item_transitions if transition[1] == token]
            events += ["R" + str(productions.index(item.production)) for item
                       in reductions if token in item.follow_set]
            event_dict[token] = events
        
        for nt in nonterminals:
            events = [str(transition[2]) for transition in item_transitions
                      if transition[1] == nt]
            event_dict[nt] = events

        table.append(event_dict)

    return table, item_sets
