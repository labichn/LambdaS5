(*

Strategy:

The machine is the transition function wrapped in a fixpoint. The transition
may not have the same input and output (a-la timestamped frontier + deltas), so
there should be an additional function to tie the output to the input. I also
need injection, which handles things like compilation, alpha uniqueness, et
cetera.

Step is the thing I don't want to rewrite. I need step to be abstract enough
that I can run with any setup. That means step's context can't have any widening
in it. I can do a simple widening in the fixpoint and then just convert the
context when I need to. So, step's context must be full.

*)


