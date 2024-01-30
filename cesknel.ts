import peggy from "npm:peggy@latest";
const grammar = await Deno.readTextFile("./sexpr.pegjs");
const parser = peggy.generate(grammar);

type Atom = { type: 'atom', value: string };
type Pair = { type: 'pair', left: Sexpr, right: Sexpr };
type Sexpr = Atom | Pair

// Same as ceknel, but with a global state

// State is global & implicit
let store: Map<string, Sexpr> = new Map();

const builtin_definitions = new Map<string, Sexpr>(Object.entries({

  '$set!': parser.parse(`(krnl env cc (symbol expr)
    (env expr (
      (result . (env ($set!-helper symbol result) cc))
    ))
  )`),

  '$car': parser.parse(`(krnl env cc ((head . tail))
    (env ($quote head) cc)
  )`),

  '$cdr': parser.parse(`(krnl env cc ((head . tail))
    (env ($quote tail) cc)
  )`),

  'cons': parser.parse(`(krnl env cc (a b)
    (env a (
      (evaluated_a . (env b (
        (evaluated_b . (env ($quote (evaluated_a . evaluated_b)) cc))
      )))
    ))
  )`),

  $amb: parser.parse(`(krnl env cc options
    (env ($quote options) (
      (($quote nil) . (env (amb-fail) halt))
      ((first . rest) . (env ($sequence
        ($set! old_fail amb-fail)
        ($set! amb-fail ($quote (krnl local_env ignored_local_cc ($quote nil)
          (local_env ($sequence
            ($set! amb-fail old_fail)
            ($amb . rest)) cc)
        )))
        first) cc))
    ))
  )`),

  'amb-assert': parser.parse(`(krnl env cc (condition)
    (env condition (
      (($quote #t) . (env ($quote #inert) cc))
      (($quote #f) . (env (amb-fail) cc))
    ))
  )`),

  'amb-fail': parser.parse(`(krnl env cc ($quote nil)
    (env ($quote FAILED_TO_AMB) halt)
  )`),

  inc: parser.parse(`(krnl env cc (value)
    (env value (
      (result . (env ($add (S) result) cc))
    ))
  )`),

  $add: parser.parse(`(krnl env cc (a b)
    (env ($quote a) (
      (($quote nil) . (env ($quote b) cc))
      ((($quote S) . rest) . (env ($add rest (S . b)) cc))
    ))
  )`),

  add: parser.parse(`(krnl env cc (a b)
    (env a (
      (evaluated_a . (env b (
        (evaluated_b . (env ($add evaluated_a evaluated_b) cc))
      )))
    ))
  )`),

  $and: parser.parse(`(krnl env cc conditions
    (env ($quote conditions) (
      (($quote nil) . (env ($quote #t) cc))
      ((first . rest) . (env first (
        (($quote #t) . (env ($and . rest) cc))
        (($quote #f) . (env ($quote #f) cc))
      )))
    ))
  )`),

  $let: parser.parse(`(krnl env cc (bindings expression)
    (env ($quote bindings) (
      (($quote nil) . (env expression cc))
      (((symbol expr) . rest) . (env expr (
        (expr_result . (((symbol . expr_result) . env) ($let rest expression) cc))
      )))
    ))
  )`),

  'equal?': parser.parse(`(krnl env cc (a b)
    (env a (
      (evaluated_a . (env b (
        (evaluated_b . (env ($equal? evaluated_a evaluated_b) cc))
      )))
    ))
  )`),

  $sequence: parser.parse(`(krnl env cc expressions
    (env ($quote expressions) (
      (($quote nil) . (env ($quote #inert) cc))
      ((single) . (env single cc))
      ((first . rest) . (env first (
        (#ignore . (env ($sequence . rest) cc))
      )))
    ))
  )`),

  list: parser.parse(`(krnl env cc objects
    (env ($quote objects) (
      (($quote nil) . (env ($quote nil) cc))
      ((first . rest) . (env first (
        (first_result . (env (list . rest) (
          (rest_of_list . (env ($quote (first_result . rest_of_list)) cc))
        )))
      )))
    ))
  )`),

  '$if': parser.parse(`(krnl env cc (cond body else)
    (env cond (
      (#t . (env body cc))
      (#f . (env else cc))
    ))
  )`),

  '$let/cc': parser.parse(`(krnl env cc (symbol expression)
    (env ($set! symbol ($quote cc)) ((#ignore . (env expression halt))))
  )`),

  'jump-to-cc': parser.parse(`(krnl env cc (target_cc)
    (env target_cc (
      (result . (env ($quote #inert) result))
    ))
  )`),

  one: parser.parse(`(S)`),
  two: parser.parse(`(S S)`),
  three: parser.parse(`(S S S)`),
  1: parser.parse(`(S)`),
  2: parser.parse(`(S S)`),
  3: parser.parse(`(S S S)`),
  S: parser.parse(`S`),
  '#t': parser.parse(`#t`),
  '#f': parser.parse(`#f`),
}))

// const initial_expr = parser.parse(`
// ($sequence
//   ($set! x 1) 
//   ($set! y 2) 
//   (add x y))`)

const initial_expr = parser.parse(`
($let ((x ($amb 1 2 3)))
  ($sequence
    (amb-assert (equal? x 2))
    x))`)

// not working :(
// const initial_expr = parser.parse(`
// ($let ((x 2)
//        (y ($amb 1 2 3)))
//   ($sequence
//     (amb-assert (equal? y 2))
//     (amb-assert (equal? x 2))
//     (cons x y)))`)

const DEFAULT_ENV: Sexpr = toSList(
  [...builtin_definitions.entries()].map(([symbol, value]) => {
    return doPair(doAtom(symbol), value);
  })
);

const initial_state: Sexpr = toSList([
  DEFAULT_ENV,
  initial_expr,
  parser.parse(`halt`),
])

let log_of_last_action = 'STARTED';

let turn_n = 0;
function step(cur_state: Sexpr): Sexpr | false {
  const [env, expr, cc] = fromSListAssertLen(cur_state, 3);
  turn_n += 1;

  if (expr.type === "pair") {
    if (expr.left.type === "atom" && expr.left.value === "$quote") {
      if (cc.type === "atom" && cc.value === "halt") {
        // FINAL_QUOTE
        const [_, final_value] = fromSListAssertLen(expr, 2);
        log_of_last_action = 'final value: ' + ast2str(final_value);
        return false;
      } else {
        // QUOTE_INTO_CC
        const [_, value] = fromSListAssertLen(expr, 2);
        const rules: Pair[] = assertListOfPairs(fromSList(cc));
        for (const rule of rules) {
          const bindings = parameter_match(rule.left, value);
          if (bindings === null) continue;
          const bindings_map = new Map<string, Sexpr>(bindings.map(({ symbol, value }) => [symbol, value]));
          log_of_last_action = 'QUOTE_INTO_CC: changed symbols: ' + bindings.map(({ symbol }) => symbol).join(', ');
          return parameter_apply(bindings_map, rule.right);
        }
        throw new Error(`no cc pattern matches ${ast2str(value)}; the patterns are ${rules.map(x => ast2str(x.left)).join(', ')}`);
      }
    } else if (expr.left.type === "atom" && expr.left.value === "$equal?") {
      // EQUAL
      log_of_last_action = 'EQUAL';
      const [_, value_a, value_b] = fromSListAssertLen(expr, 3);
      if (equal(value_a, value_b)) {
        return toSList([env, parser.parse(`($quote #t)`), cc]);
      } else {
        return toSList([env, parser.parse(`($quote #f)`), cc]);
      }
    } else if (expr.left.type === "atom" && expr.left.value === "$set!-helper") {
      // $SET!
      log_of_last_action = '$SET!-HELPER';
      const [_, symbol, value] = fromSListAssertLen(expr, 3);
      if (symbol.type !== 'atom') throw new Error(`$set! got non atom symbol: ${ast2str(symbol)}`);
      // const [quote, value] = fromSListAssertLen(value_expr, 2);
      // if (quote.type !== 'atom' || quote.value !== '$quote') throw new Error();
      store.set(symbol.value, value);
      return toSList([env, parser.parse(`($quote #inert)`), cc]);
    } else if (expr.left.type === "pair" && expr.left.left.type === "atom" && expr.left.left.value === "krnl") {
      // KRNL
      const params = expr.right;
      const [_, env_name, cc_name, params_name, naive_body] = fromSListAssertLen(expr.left, 5);
      if (env_name.type !== 'atom' || cc_name.type !== 'atom') throw new Error(`bad krnl, env_name is ${ast2str(env_name)} & cc_name is ${ast2str(cc_name)}`);
      const param_bindings = parameter_match(params_name, params);
      if (param_bindings === null) throw new Error(`bad krnl application: pattern is ${ast2str(params_name)}, but got values ${ast2str(params)}`);
      const body = make_unique_cc_names(naive_body, turn_n);
      const bindings_map = new Map<string, Sexpr>(param_bindings.map(({ symbol, value }) => [symbol, value]));
      bindings_map.set(env_name.value, env);
      bindings_map.set(cc_name.value, cc);
      log_of_last_action = 'KRNL:';
      return parameter_apply(bindings_map, body);
    } else {
      // EVAL_HEAD
      log_of_last_action = 'EVAL_HEAD:';
      return toSList([env, expr.left, toSList([
        doPair(
          doAtom(`evaluated_head_${turn_n}`),
          toSList([env, doPair(doAtom(`evaluated_head_${turn_n}`), expr.right), cc])
        )
      ])]);
    }
  } else {
    // ENV_LOOKUP
    log_of_last_action = 'ENV_LOOKUP:';
    const value = lookup(env, expr.value);
    if (value === null) throw new Error(`undefined symbol: ${expr.value}`);
    return toSList([env, toSList([doAtom('$quote'), value]), cc]);
  }
}

function make_unique_cc_names(state: Sexpr, id: number): Sexpr {
  // return state;
  const [env, expr, cc] = fromSListAssertLen(state, 3);
  if (cc.type === "atom") return state;
  const naive_patterns = fromImproperList(cc);

  // const patterns: Pair[] = assertListOfPairs(fromSList(cc));
  const patterns: Pair[] = assertListOfPairs(naive_patterns.list);
  const new_cc = toSList(patterns.map(rule => {
    const [new_pattern, var_names] = asdf(rule.left, id);
    const naive_new_template = qwerty(rule.right, var_names, id);
    if (naive_new_template.type === "atom") {
      return doPair(new_pattern, naive_new_template);
    }
    const new_template = make_unique_cc_names(naive_new_template, id);
    return doPair(new_pattern, new_template);
  }));

  return toSList([env, expr, new_cc]);

  function asdf(pattern: Sexpr, id: number): [Sexpr, string[]] {
    if (pattern.type === "pair" && pattern.left.type === "atom" && pattern.left.value === "$quote") {
      // literal match, leave alone
      return [pattern, []];
    } else {
      if (pattern.type === "atom") {
        // assume that nil is never written by the user & leave it alone
        if (pattern.value === "nil") return [pattern, []];
        // same for #ignore
        if (pattern.value === "#ignore") return [pattern, []];

        return [doAtom(pattern.value + `_${id}`), [pattern.value]];
      } else {
        const [new_left, left_names] = asdf(pattern.left, id);
        const [new_right, right_names] = asdf(pattern.right, id);
        return [
          doPair(new_left, new_right),
          [...left_names, ...right_names]
        ];
      }
    }
  }

  function qwerty(template: Sexpr, var_names: string[], id: number): Sexpr {
    if (template.type === "atom") {
      if (var_names.includes(template.value)) {
        return doAtom(template.value + `_${id}`);
      } else {
        return template;
      }
    } else {
      const new_left = qwerty(template.left, var_names, id);
      const new_right = qwerty(template.right, var_names, id);
      return doPair(new_left, new_right);
    }
  }
}

function lookup(env: Sexpr, symbol: string): Sexpr | null {
  if (store.has(symbol)) return store.get(symbol)!;
  const pairs = fromSList(env);
  for (const pair of pairs) {
    if (pair.type !== "pair") throw new Error("bad env, entry is not a pair");
    if (pair.left.type !== "atom") throw new Error("bad env, symbol is not atom")
    if (pair.left.value === symbol) return pair.right;
  }
  return null;
}


function state2str(state: Sexpr, indent = 0): string {
  const [env, expr, cc] = fromSListAssertLen(state, 3);
  const [env_str, expr_str, cc_str] = helper(env, expr, cc, indent);
  return `(\n${[env_str, expr_str, cc_str].join('\n')}\n${'\t'.repeat(indent)})`

  function helper(env: Sexpr, expr: Sexpr, cc: Sexpr, indent: number): string[] {
    return [
      '\t'.repeat(indent + 1) + ast2str(env),
      '\t'.repeat(indent + 1) + ast2str(expr),
      cc_helper(cc, indent + 1),
    ]
  }

  function cc_helper(cc: Sexpr, indent: number): string {
    const spacing = '\t'.repeat(indent);
    if (cc.type === "atom") {
      return spacing + cc.value;
    }
    const rules = assertListOfPairs(fromSList(cc));
    return `${spacing}(\n${rules.map(rule => {
      return `${spacing}\t(${ast2str(rule.left)} . ${state2str(rule.right, indent + 1)})`
    }).join('\n')}\n${spacing})`
    // return ast2str(cc);
  }

  // return [`env: ${ast2str(env)}`, `expr: ${ast2str(expr)}`, `cc: ${ast2str(cc)}`].join('\n');
}

function doAtom(value: string): Atom {
  return { type: "atom", value: value };
}

function doPair(left: Sexpr, right: Sexpr): Pair {
  return { type: "pair", left, right };
}

function ensureAtom(value: Sexpr): Atom {
  if (value.type === "pair") throw new Error(`expected atom but got ${ast2str(value)}`);
  return value;
}

function findBuiltinName(ast: Sexpr): string | null {
  let builtin_name: string | null = null;
  builtin_definitions.forEach((value, name) => {
    if (builtin_name === null && equal(ast, value)) {
      builtin_name = name;
    }
  });
  if (builtin_name !== null) return `[${builtin_name}]`;
  return null;
}

// TODO: prettier
function ast2str(ast: Sexpr): string {
  if (ast.type === "atom") return ast.value;

  if (equal(ast, DEFAULT_ENV)) return '[BUILTIN_ENV]'

  const builtin_name = findBuiltinName(ast);
  if (builtin_name !== null) return builtin_name;

  if (equal(ast.right, DEFAULT_ENV)) {
    return `(${ast2str(ast.left)} . [BUILTIN_ENV])`;
  }

  const builtin_name_right = findBuiltinName(ast.right);
  if (builtin_name_right !== null) {
    return `(${ast2str(ast.left)} . ${builtin_name_right})`
  }


  const asdf = fromImproperList(ast);
  if (asdf.sentinel.value === "nil") {
    return `(${asdf.list.map(x => ast2str(x)).join(' ')})`;
  } else {
    return `(${asdf.list.map(x => ast2str(x)).join(' ')} . ${asdf.sentinel.value})`;
    // return `(${ast2str(ast.left)} . ${ast2str(ast.right)})`
  }
}

function equal(a: Sexpr, b: Sexpr): boolean {
  if (a.type === "atom") {
    return b.type === "atom" && b.value === a.value;
  } else {
    return b.type === "pair" && equal(a.left, b.left) && equal(a.right, b.right);
  }
}

function parameter_match(pattern: Sexpr, value: Sexpr): null | { symbol: string, value: Sexpr }[] {
  if (pattern.type === "pair" && pattern.left.type === "atom" && pattern.left.value === "$quote") {
    // literal match
    const [_, target] = fromSListAssertLen(pattern, 2);
    if (equal(target, value)) {
      return [];
    } else {
      return null;
    }
  } else {
    if (pattern.type === "atom") {
      // assume that nil is never written by the user & leave it alone
      if (pattern.value === "nil") {
        if (value.type !== "atom" || value.value !== "nil") {
          return null;
        } else {
          return [];
        }
      }
      // same for #ignore
      if (pattern.value === "#ignore") return [];

      return [{ symbol: pattern.value, value }];
    } else {
      if (value.type !== "pair") return null;
      const match_left = parameter_match(pattern.left, value.left);
      const match_right = parameter_match(pattern.right, value.right);
      if (match_left === null || match_right === null) return null;
      return [...match_left, ...match_right];
    }
  }
}

function parameter_apply(bindings: Map<string, Sexpr>, template: Sexpr): Sexpr {
  if (template.type === "atom") {
    const value = bindings.get(template.value);
    return (value === undefined) ? template : value;
  } else {
    return doPair(
      parameter_apply(bindings, template.left),
      parameter_apply(bindings, template.right),
    );
  }
}

function toSList(values: Sexpr[]): Sexpr {
  if (values.length === 0) {
    return doAtom("nil");
  } else {
    return doPair(values[0], toSList(values.slice(1)));
  }
}

function fromSList(slist: Sexpr): Sexpr[] {
  if (slist.type === "atom") {
    if (slist.value === "nil") return [];
    throw new Error(`list doesn't end in nil, it ends in: ${slist.value}`);
  } else {
    return [slist.left, ...fromSList(slist.right)];
  }
}

function fromSListAssertLen(slist: Sexpr, len: number): Sexpr[] {
  const result = fromSList(slist);
  if (result.length !== len) {
    throw new Error(`expected len ${len}, got len ${result.length} from slist ${ast2str(slist)}`);
  }
  return result;
}

function assertListOfPairs(lst: Sexpr[]): Pair[] {
  if (lst.some(v => v.type !== "pair")) {
    throw new Error(`not all are pairs: ${lst.map(x => ast2str(x)).join(', ')}`);
  }
  // @ts-ignore: the above already checks the type
  return lst;
}

function fromImproperList(expr: Sexpr): { list: Sexpr[], sentinel: Atom } {
  if (expr.type === "atom") {
    return { list: [], sentinel: expr };
  } else {
    const asdf = fromImproperList(expr.right);
    return { list: [expr.left, ...asdf.list], sentinel: asdf.sentinel };
  }
}

if (import.meta.main) {
  let cur_state: Sexpr | false = initial_state;
  while (cur_state != false) {
    await Deno.writeTextFile("./log.txt", log_of_last_action + '\n' + state2str(cur_state) + '\n\n', {
      append: true,
    });
    // console.log(state2str(cur_state), '\n');
    // alert();
    cur_state = step(cur_state);
  }
  await Deno.writeTextFile("./log.txt", log_of_last_action, {
    append: true,
  });
  console.log(log_of_last_action);
}
