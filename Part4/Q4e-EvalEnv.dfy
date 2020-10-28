include "WFFSupport.dfy"
include "Q4a-names.dfy"
include "Q4b-eval.dfy"

lemma EvalEnv(e: WFF, n: string, env: Env)
  requires n in env
  requires forall nn : string :: nn in names(e) ==> nn in env
  ensures eval(e, env)
       == eval(substitute(e, n, env[n]), (map k | k in env && k != n :: env[k])) { }

function method substitute(e: WFF, n: string, c: bool): (r: WFF )
  ensures n !in names(r) { e }