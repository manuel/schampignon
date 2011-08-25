// An interpreter for a Kernel-like language.
// By Manuel Simoni <msimoni@gmail.com>, August 2011
// In the public domain.

/**** Virtual Machine ****/

function Scm_vm(e)
{
    // Accumulator
    this.a = null;
    // neXt instruction
    this.x = null;
    // Environment
    this.e = e;
    // Stack
    this.s = null;
}

function Scm_frame(x, e, s)
{
    this.x = x;
    this.e = e;
    this.s = s;
}

/**** Evaluation ****/

function scm_eval(vm, form)
{
    scm_compile(vm, form, scm_insn_halt, false);
    while(vm.x(vm));
    return vm.a;
}

function scm_compile(vm, form, next, tail)
{
    if (scm_is_symbol(form)) {
        vm.a = scm_lookup(vm.e, form);
        vm.x = next;
    } else if (scm_is_non_nil_compound(form)) {
        var combiner = scm_car(form);
        var operand_tree = scm_cdr(form);
        scm_compile(vm, combiner, scm_insn_combine(operand_tree, next, tail), false);
    } else {
        vm.a = form;
        vm.x = next;
    }
}

function scm_insn_combine(otree, next, tail)
{
    return function(vm) {
        return vm.a.scm_combine(vm, otree, next, tail);
    };
}

function scm_insn_return(vm)
{
    vm.x = vm.s.x;
    vm.e = vm.s.e;
    vm.s = vm.s.s;
    return true;
}

function scm_insn_halt(vm)
{
    return false;
}

/**** Compound Combiners & Applicatives ****/

function Scm_combiner(env, ptree, eformal, body)
{
    // Static lexical environment link
    this.env = env;
    // Parameter tree
    this.ptree = ptree;
    // Dynamic lexical environment parameter
    this.eformal = eformal;
    // Body form
    this.body = body;
}

function Scm_wrapper(combiner)
{
    // Underlying combiner
    this.combiner = combiner;
}

Scm_combiner.prototype.scm_combine = scm_general_combine;
Scm_wrapper.prototype.scm_combine  = scm_general_combine;

function scm_general_combine(vm, otree, next, tail)
{
    if (!tail) {
        vm.s = new Scm_frame(next, vm.e, vm.s);
        next = scm_insn_return;
    }
    if (scm_is_applicative(vm.a)) {
        /* For an applicative, we take a detour through argument
           evaluation.  This ping-pongs between scm_insn_argument_eval
           and scm_insn_argument_store, destructuring the operand
           tree, and building up the arguments list, until the operand
           tree is empty. */
        vm.x = scm_insn_argument_eval(scm_unwrap(vm.a), otree, [], next);
    } else {
        vm.e = scm_extend(vm.a, otree, vm.e);
        scm_compile(vm, vm.a.body, next, true);
    }
    return true;
}

function scm_insn_argument_eval(combiner, otree, args, next)
{
    return function(vm) {
        if (scm_nullp(otree)) {
            var combination = scm_cons(combiner, scm_array_to_cons_list(args));
            /* After argument evaluation of an original applicative
               combination, tail-call the new combination.  If the
               original combination was not a tail call, it has
               created a new frame, which we can reuse.  If the
               original combination was a tail call, it's the same:
               just reuse its frame. */
            scm_compile(vm, combination, next, true);
        } else {
            var operand = scm_car(otree);
            otree = scm_cdr(otree);
            next = scm_insn_argument_store(combiner, otree, args, next);
            scm_compile(vm, operand, next, false);
        }
        return true;
    };
}

function scm_insn_argument_store(combiner, otree, args, next)
{
    return function(vm) {
        args.push(vm.a);
        vm.x = scm_insn_argument_eval(combiner, otree, args, next);
        return true;
    };
}

/**** Built-in Combiners ****/

/* $vau */

function Scm_vau() {}

Scm_vau.prototype.scm_combine = function(vm, otree, next, tail)
{
    var ptree = scm_compound_elt(otree, 0);
    var eformal = scm_compound_elt(otree, 1);
    var body = scm_compound_elt(otree, 2);
    vm.a = new Scm_combiner(vm.e, ptree, eformal, body);
    vm.x = next;
    return true;
}

/* $define! */

function Scm_define() {}

Scm_define.prototype.scm_combine = function(vm, otree, next, tail)
{
    var ptree = scm_compound_elt(otree, 0);
    var expr = scm_compound_elt(otree, 1);
    scm_compile(vm, expr, scm_insn_define(ptree, vm.e, next), false);
    return true;
}

function scm_insn_define(ptree, env, next)
{
    return function(vm) {
        scm_match(env, ptree, vm.a);
        vm.x = next;
        return true;
    };
}

/* $if */

function Scm_if() {}

Scm_if.prototype.scm_combine = function(vm, otree, next, tail)
{
    var test = scm_compound_elt(otree, 0);
    var consequent = scm_compound_elt(otree, 1);
    var alternative = scm_compound_elt(otree, 2);
    scm_compile(vm, test, scm_insn_test(consequent, alternative, next, tail), false);
    return true;
}

function scm_insn_test(consequent, alternative, next, tail)
{
    return function(vm) {
        scm_compile(vm, vm.a ? consequent : alternative, next, tail);
        return true;
    };
}

/* eval */

function Scm_eval() {}

Scm_eval.prototype.scm_combine = function(vm, args, next, tail)
{
    var expr = scm_compound_elt(args, 0);
    var env = scm_compound_elt(args, 1);
    vm.e = env;
    scm_compile(vm, expr, next, tail);
    return true;
}

/* call/cc */

function Scm_callcc() {}

Scm_callcc.prototype.scm_combine = function(vm, args, next, tail)
{
    var fun = scm_compound_elt(args, 0);
    var k = scm_wrap(new Scm_cont(vm.s));
    scm_compile(vm, scm_cons(fun, scm_cons(k, scm_nil)), next, tail);
    return true;
}

function Scm_cont(s)
{
    this.s = s;
}

Scm_cont.prototype.scm_combine = function(vm, args, next, tail)
{
    var value = scm_compound_elt(args, 0);
    vm.a = value;
    vm.x = scm_insn_return;
    vm.s = this.s;
    return true;
}

/**** Native Combiners ****/

function Scm_native(js_fun)
{
    this.js_fun = js_fun;
}

Scm_native.prototype.scm_combine = function(vm, args, next, tail)
{
    var argslist = scm_cons_list_to_array(args);
    vm.a = this.js_fun.apply(null, argslist);
    vm.x = next;
    return true;
}

function scm_make_native(js_fun)
{
    return scm_wrap(new Scm_native(js_fun));
}

/**** Schampignon Hare-Brained Bare-Bones Object System (SCHHBBBOS) ****/

function scm_make_vtable()
{
    return {};
}

function scm_make_instance(vt)
{
    return { scm_vt: vt };
}

function scm_bind_method(vt, symbol, method)
{
    vt[symbol] = method;
}

function scm_lookup_method(obj, symbol)
{
    var method = obj.scm_vt[symbol];
    if (!method) scm_error("message not understood: " + symbol);
    return method;
}

function scm_set_slot(obj, symbol, value)
{
    obj[symbol] = value;
}

function scm_get_slot(obj, symbol)
{
    var value = obj[symbol];
    scm_assert(value !== undefined);
    return value;
}

/**** Environments ****/

function Scm_env(parent)
{
    this.parent = parent;
    this.bindings = {};
}

function scm_make_env(parent)
{
    return new Scm_env(parent);
}

function scm_lookup(env, name)
{
    var value = env.bindings[name];
    if (value !== undefined) {
        return value;
    } else {
        if (env.parent)
            return scm_lookup(env.parent, name);
        else
            scm_error("undefined variable:" + name);
    }
}

function scm_update(env, name, value)
{
    env.bindings[name] = value;
}

function scm_extend(combiner, otree, denv)
{
    var xenv = scm_make_env(combiner.env);
    scm_match(xenv, combiner.ptree, otree);
    // todo: handle %ignore
    scm_update(xenv, combiner.eformal, denv);
    return xenv;
}

function scm_match(env, formal_tree, actual_tree)
{
    if (scm_nullp(formal_tree)) {
        if (!scm_nullp(actual_tree))
            scm_error("match failure: expected nil, got " + actual_tree);
    } else if (scm_is_non_nil_compound(formal_tree)) {
        scm_match(env, scm_car(formal_tree), scm_car(actual_tree));
        scm_match(env, scm_cdr(formal_tree), scm_cdr(actual_tree));
    } else if (scm_is_symbol(formal_tree)) {
        scm_update(env, formal_tree, actual_tree);
    } else {
        scm_error("match failure: invalid formal: " + formal_tree);
    }
    // todo: handle %ignore
}

/**** Forms ****/

var scm_nil = null;

function scm_cons(car, cdr)
{
    return [car, cdr];
}

function scm_car(cons)
{
    scm_assert(scm_is_non_nil_compound(cons));
    return cons[0];
}

function scm_cdr(cons)
{
    scm_assert(scm_is_non_nil_compound(cons));
    return cons[1];
}

function scm_is_symbol(x)
{
    return (typeof(x) === "string");
}

function scm_is_compound(x)
{
    return (scm_nullp(x)) || scm_is_non_nil_compound(x);
}

function scm_is_non_nil_compound(x)
{
    return (x instanceof Array);
}

function scm_nullp(c)
{
    return c === scm_nil;
}

function scm_compound_elt(x, i)
{
    scm_assert(scm_is_non_nil_compound(x));
    scm_assert(i >= 0);
    while(i > 0) {
        x = scm_cdr(x);
        i--;
    }
    return scm_car(x);
}

function scm_array_to_cons_list(array, end)
{
    var c = end ? end : scm_nil;
    for (var i = array.length; i > 0; i--)
        c = scm_cons(array[i - 1], c);
    return c;
}

function scm_cons_list_to_array(c)
{
    scm_assert(scm_is_compound(c));
    var res = [];
    while(!scm_nullp(c)) {
        res.push(scm_car(c));
        c = scm_cdr(c);
    }
    return res;
}

/**** Utilities ****/

function scm_wrap(combiner)
{
    return new Scm_wrapper(combiner);
}

function scm_unwrap(wrapper)
{
    return wrapper.combiner;
}

function scm_is_applicative(combiner)
{
    return (combiner instanceof Scm_wrapper);
}

function scm_is_operative(combiner)
{
    return !scm_is_applicative(combiner);
}

function scm_eq(a, b)
{
    return a === b;
}

function scm_plus(a, b)
{
    return a + b;
}

function scm_assert(b)
{
    if (!b) scm_error("assertion failed");
}

function scm_error(msg)
{
    throw msg;
}

/**** Parser ****/

/* Returns an array of cons lists of the forms in the string. */
function scm_parse(string)
{
    var result = scm_program_syntax(ps(string));
    if (result.ast) {
        return result.ast;
    } else {
        return scm_error("Reader error", string);
    }
}

var scm_expression_syntax =
    function(input) { return scm_expression_syntax(input); }; // forward decl.

var scm_digits = 
    join_action(repeat1(range("0", "9")), "");

var scm_number_syntax =
    action(sequence(optional(choice("+", "-")),
                    scm_digits,
                    optional(join_action(sequence(".", scm_digits), ""))),
           scm_number_syntax_action);

function scm_number_syntax_action(ast)
{    
    var sign = ast[0] ? ast[0] : "+";
    var integral_digits = ast[1];
    var fractional_digits = ast[2] || "";
    return Number(sign + integral_digits + fractional_digits);
}

var scm_identifier_special_char =
    choice(// R5RS sans "."
           "-", "&", "!", ":", "=", ">","<", "%", "+", "?", "/", "*", "#",
           // Additional
           "$", "_");

var scm_identifier_syntax =
    action(join_action(repeat1(choice(range("a", "z"),
                                      range("0", "9"),
                                      scm_identifier_special_char)),
                       ""),
           scm_identifier_syntax_action);

function scm_identifier_syntax_action(ast)
{
    return ast;
}

var scm_nil_syntax =
    action("()", scm_nil_syntax_action);

function scm_nil_syntax_action(ast)
{
    return scm_nil;
}

var scm_dot_syntax =
    action(wsequence(".", scm_expression_syntax),
           scm_dot_syntax_action);

function scm_dot_syntax_action(ast)
{
    return ast[1];
}

var scm_compound_syntax =
    action(wsequence("(",
                     repeat1(scm_expression_syntax),
                     optional(scm_dot_syntax),
                     ")"),
           scm_compound_syntax_action);

function scm_compound_syntax_action(ast)
{
    var exprs = ast[1];
    var end = ast[2] ? ast[2] : scm_nil;
    return scm_array_to_cons_list(exprs, end);
}

var scm_expression_syntax =
    whitespace(choice(scm_number_syntax,
                      scm_nil_syntax,
                      scm_compound_syntax,
                      scm_identifier_syntax));

var scm_program_syntax =
    whitespace(repeat1(scm_expression_syntax));
