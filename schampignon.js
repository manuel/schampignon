// An interpreter for a Kernel-like language.
// By Manuel Simoni <msimoni@gmail.com>, August 2011
// In the public domain.

/**** Virtual Machine ****/

function Scm_vm()
{
    // Accumulator
    this.a = null;
    // neXt instruction
    this.x = null;
    // Environment
    this.e = new Scm_env();
    // evaluated operands (aRguments)
    this.r = [];
    // Unevaluated operands
    this.u = scm_nil;
    // Stack
    this.s = null;
}

function Scm_frame(x, e, r, u, s)
{
    this.x = x;
    this.e = e;
    this.r = r;
    this.u = u;
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
        var otree = scm_cdr(form);
        scm_compile(vm, combiner, scm_insn_combine(otree, next, tail), false);
    } else {
        vm.a = form;
        vm.x = next;
    }
}

/* Dispatch to scm_combine method of combiner in accumulator. */
function scm_insn_combine(otree, next, tail)
{
    return function(vm) {
        return vm.a.scm_combine(vm, otree, next, tail);
    };
}

/* This is the scm_combine method of both compound operatives and
   applicatives.  Built-ins such as $define! and $vau have their own,
   different methods. */
function scm_general_combine(vm, otree, next, tail)
{
    if (!tail) vm.s = scm_make_frame(next, vm.e, vm.r, vm.u, vm.s);
    vm.r = [];
    if (scm_is_applicative(vm.a)) {
        /* For applicatives, make a detour through argument evaluation. */
        var combiner = scm_unwrap(vm.a);
        vm.u = otree;
        vm.x = scm_insn_argument_eval(combiner, next, tail);
    } else {
        /* Operatives are entered directly. */
        scm_enter(vm, vm.a, otree, next, tail);
    }
    return true;
}

function scm_enter(vm, combiner, otree, next, tail)
{
    vm.e = scm_extend(vm.e, combiner, otree);
    scm_compile(vm, combiner.body, tail ? next : scm_insn_return, true);
}

/* Argument evaluation works by ping-ponging between argument_eval and
   argument_store, until all arguments are evaluated. */
function scm_insn_argument_eval(combiner, next, tail)
{
    return function(vm) {
        if (scm_is_non_nil_compound(vm.u)) {
            var operand = scm_car(vm.u);
            vm.u = scm_cdr(vm.u);
            scm_compile(vm, operand, scm_insn_argument_store(combiner, next, tail), false);
            return true;
        } else {
            scm_enter(vm, combiner, scm_array_to_cons_list(vm.r), next, tail);
            return true;
        }
    };
}

function scm_insn_argument_store(combiner, next, tail)
{
    vm.r.push(vm.a);
    vm.x = scm_insn_argument_eval(combiner, next, tail);
    return true;
}

/* Pop the stack, restoring the saved registers. */
function scm_insn_return(vm)
{
    vm.x = vm.s.x;
    vm.e = vm.s.e;
    vm.r = vm.s.r;
    vm.u = vm.s.u;
    vm.s = vm.s.s;
    return true;
}

function scm_insn_halt(vm)
{
    return false;
}

/**** Built-in Combiners ****/

// ($vau ptree eformal body)

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

// ($define! ptree expr)

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

/**** Compound Combiners ****/

function Scm_combiner(env, ptree, eformal, body)
{
    this.env = env;
    this.ptree = ptree;
    this.eformal = eformal;
    this.body = body;
}

Scm_combiner.prototype.scm_combine = scm_general_combine;

/**** Wrappers (Applicatives) ****/

function Scm_wrapper(combiner)
{
    this.combiner = combiner;
}

Scm_wrapper.prototype.scm_combine = scm_general_combine;

function scm_wrap(combiner)
{
    return new Scm_wrapper(combiner);
}

function scm_unwrap(applicative)
{
    scm_assert(scm_is_applicative(combiner));
    return applicative.combiner;
}

function scm_is_applicative(combiner)
{
    return (combiner instanceof Scm_wrapper);
}

/**** Environments ****/

function Scm_env(parent)
{
    this.parent = parent;
    this.bindings = {};
}

function scm_lookup(env, name)
{
    var value = scm_just_lookup(env, name);
    if (value !== undefined) {
        return value;
    } else {
        if (env.parent)
            return scm_lookup(env.parent, name);
        else
            scm_error("undefined variable");
    }
}

function scm_just_lookup(env, name)
{
    return env.bindings[name];
}

function scm_update(env, name, value)
{
    if (scm_just_lookup(env, name) !== undefined) {
        scm_just_update(env, name, value);
    } else {
        if (env.parent)
            scm_update(env.parent, name, value);
        else
            scm_just_update(env, name, value);
    }
}

function scm_just_update(env, name, value)
{
    env.bindings[name] = value;
}

function scm_extend(denv, combiner, otree)
{
    var xenv = new Scm_env(combiner.env);
    /* This should really destructure the operand tree according to
       the parameter tree. */
    scm_just_update(xenv, combiner.ptree, otree);
    scm_just_update(xenv, combiner.eformal, denv);
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
    return (x === scm_nil) || scm_is_non_nil_compound(x);
}

function scm_is_non_nil_compound(x)
{
    return (x instanceof Array);
}

function scm_compound_operator(x)
{
    return scm_car(x);
}

function scm_compound_elt(x, i)
{
    scm_assert(scm_is_non_nil_compound(x));
    var c = x;
    while(i > 0) {
        c = scm_cdr(x);
        i--;
    }
    return scm_car(c);
}

function scm_array_to_cons_list(array)
{
    var c = scm_nil;
    for (var i = array.length; i > 0; i--)
        c = scm_cons(array[i - 1], c);
    return c;
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
