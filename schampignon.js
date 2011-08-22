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
    } else if (scm_is_compound(form)) {
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

/**** Compound Combiners ****/

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

Scm_combiner.prototype.scm_combine = function(vm, otree, next, tail)
{
    if (!tail) vm.s = new Scm_frame(next, vm.e, vm.s);
    vm.e = scm_extend(vm.e, vm.a, otree);
    scm_compile(vm, vm.a.body, tail ? next : scm_insn_return, true);
    return true;
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
    scm_compile(vm, expr, scm_insn_define(ptree, next), false);
    return true;
}

function scm_insn_define(ptree, next)
{
    return function(vm) {
        scm_update(vm.e, ptree, vm.a);
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
    var old_env = vm.e;
    vm.e = env;
    scm_compile(vm, expr, scm_insn_weird_env_reset(old_env, next), tail);
    return true;
}

/* I'm out of my depth here... */
function scm_insn_weird_env_reset(old_env, next)
{
    return function(vm) {
        vm.e = old_env;
        vm.x = next;
        return true;
    };
}

/**** Wrappers ****/

function Scm_wrapper(combiner)
{
    this.combiner = combiner;
}

Scm_wrapper.prototype.scm_combine = function(vm, otree, next, tail)
{
    vm.x = scm_insn_argument_eval(scm_unwrap(this), otree, [], next, tail);
    return true;
}

function scm_insn_argument_eval(combiner, otree, args, next, tail)
{
    return function(vm) {
        if (scm_nullp(otree)) {
            var c = scm_cons(combiner, scm_array_to_cons_list(args));
            scm_compile(vm, c, next, tail);
        } else {
            var o = scm_car(otree);
            otree = scm_cdr(otree);
            next = scm_insn_argument_store(combiner, otree, args, next, tail);
            scm_compile(vm, o, next, false);
        }
        return true;
    };
}

function scm_insn_argument_store(combiner, otree, args, next, tail)
{
    return function(vm) {
        args.push(vm.a);
        vm.x = scm_insn_argument_eval(combiner, otree, args, next, tail);
        return true;
    };
}

function scm_wrap(combiner)
{
    return new Scm_wrapper(combiner);
}

function scm_unwrap(wrapper)
{
    return wrapper.combiner;
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

/**** Environments ****/

function Scm_env(parent)
{
    this.parent = parent;
    this.bindings = {};
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

function scm_extend(denv, combiner, otree)
{
    var xenv = new Scm_env(combiner.env);
    /* This should really destructure the operand tree according to
       the parameter tree. */
    scm_update(xenv, combiner.ptree, otree);
    scm_update(xenv, combiner.eformal, denv);
    return xenv;
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

function scm_array_to_cons_list(array)
{
    var c = scm_nil;
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
    choice(// R5RS
           "-", "&", "!", ":", ".", "=", ">","<", "%", "+", "?", "/", "*", "#",
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

var scm_compound_syntax =
    action(wsequence("(", repeat0(scm_expression_syntax), ")"),
           scm_compound_syntax_action);

function scm_compound_syntax_action(ast)
{
    var forms = ast[1];
    return scm_array_to_cons_list(forms);
}

var scm_expression_syntax =
    whitespace(choice(scm_number_syntax,
                      scm_compound_syntax,
                      scm_identifier_syntax));

var scm_program_syntax =
    whitespace(repeat1(scm_expression_syntax));
