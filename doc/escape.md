# Escape analysis

This document captures some thoughts on how to reimplement escape
analysis within amigo.

## Current implementation

cmd/compile's current escape analysis pass
(cmd/compile/internal/escape) involves a few steps:

1. Parse and type check all functions within a package.
2. Break the static [call graph](https://en.wikipedia.org/wiki/Call_graph) into
   [strongly connected components](https://en.wikipedia.org/wiki/Strongly_connected_component).
   (Function literals are always forced into the same component as their enclosing function.)
3. Analyze each component in dependency order.
4. For each function body, identify statements and expressions that:
   - Allocate variables, either explicitly such as a variable
	 declaration or implicitly such as an addressed composite
	 literal;
   - Flow values from one variable to another, possibly involving
     addressing or dereferencing operations.
   - Call functions:
     + Static calls (i.e., function calls where the callee is a
       declared function, or method calls on concrete types) to
       functions within the same component are handled naively as
       flowing arguments to their parameter's variables, and flowing
       the result parameter's back as the call expression's results.
	 + Static calls to functions outside of the current component
       (including calls to imported functions) are interpreted using
       previously computed escape analysis summary data, which
       summarizes the value flows from the parameters to the heap and
       the results.
	 + Indirect calls (i.e., function calls with a variable callee, or
       interface method calls) are handled pessimistically by assuming
       parameters always flow to the heap.
5. Construct a graph with vertices representing all variables
   (including the "heap" pseudo-variable) and weighted edges
   representing all assignments/dereferences for functions within a
   given component.
6. "Solve" the graph by identifying any variables whose address flows
   to variables that may "outlive" them. These variables need to be
   heap allocated, while others can be stack allocated.
7. Additionally, for parameters, compute the shortest paths to the
   heap and result parameters, if any. Record this information as
   summary data to use in subsequent analysis rounds.

The implementation also identifies "transient" variables, whose
lifetime ends immediately after the enclosing statement. This
information is used by the "order" pass, which is responsible for
later rewriting statements to enforce Go's order-of-evaluation
semantics. For "transient" variables, their temporaries can be reused,
reducing stack frame size.

## Limitations

### Inlining

The escape analysis current implementation runs in a monolithic pass
after inlining. Running after inlining is helpful, because we normally
have to be very conservative in analyzing values that flow to result
parameters. However, post-inlining we know exactly where the values
flow, which may introduce more opportunities for stack allocation.

However, this also means the inlining pass can't use escape analysis
information to decide whether a particular function call is a good
candidate for inlining. Ideally, the inlining heuristics would favor
inlining function calls that would allow more stack allocation.

### Generics

Similarly to inlining, escape analysis also runs after instantiating
generic types/functions. Consequently, shape-based stenciling also
can't adjust based on escape analysis properties, which means the
function needs to be compiled pessimistically to assume all type
parameter method calls escape their parameters.

Again, ideally, the instantiation logic would have (at least some)
escape analysis information available for type arguments, namely their
methods that satisfy the type parameter constraints.

### Efficiency

The current design requires the full AST of all functions to be
available at once. It also involves walking the full AST of each
function twice: once for SCC, and a second time for escape analysis
itself.

It's also currently an entirely sequential process: one component is
analyzed at a time. Presumably compile-time CPU utilization would be
better if we tried analyzing independent components concurrently.

Finally, the current algorithm for identifying static function calls
(ir.StaticValue) is very primitive and also slow, because it operates
on the AST. Ideally, we could take advantage of SSA form to deduce
static function callees.

## Thoughts

I have a hypothesis that we can construct "partial" escape analysis
summaries for each function just once, based on initial AST. And then
we later combine the partial summaries into complete, final results.

Some design constraints:

1. It probably makes sense to do the partial escape analysis during
   (or adjacent to) SSA construction. In fact, x/tools/go/ssa already
   implements a naive escape analysis pass entirely during SSA
   construction.
   - Concretely, I anticipate we can record data flows during SSA
     construction, and then apply a lightweight optimization pass just
     to filter redundant data flows before serializing them.
2. The partial escape analysis results will need to be possible to
   instantiate multiple times, similar to how inlining needs to
   instantiate function bodies multiple times. This means supporting
   transitive instantiation too (e.g., if `f` calls `g`, `g` calls
   `h`, and both `g` and `h` are inlined into `f`; then we need both
   `g` and `h`'s partial escape analysis information for doing a full
   analysis of `f`).
3. Partial analysis must work on type-parameterized functions and
   methods. In particular, we need to account for implicit
   addressing/dereferencing that might vary depending on concrete type
   arguments. E.g., `range x` implies a dereference if `x` has type
   `[]int` or `*[N]int`, but not `[N]int`.
4. Analysis of function calls (particularly indirect function calls)
   will probably need a way to link the function callee SSA value with
   the incoming/outgoing flow edges.
   - Maybe even incorporate directly into the SSA value graph, like
     x/tools/go/ssa.DebugRef?

Alternatively/additionally, it should be possible to perform escape
analysis on the resulting SSA instead. As a debugging aid, it might be
interesting to implement a separate escape analysis graph construction
pass that operates exclusively on the final SSA form, to identify
cases where the combined partial summaries are giving incorrect or
suboptimal results.

In fact, there are most certainly cases where SSA optimizations could
narrow down escape analysis results (e.g., identifying unreachable
code paths, and thus unreachable data flows). So the partial analysis
results may only be useful for cross-function optimization decisions
like inlining and stenciling, and then we want a fully precise
analysis based on the final, optimized SSA representation (or as late
as we're allowed to push escape analysis).

## Further opportunities

### Non-exported interface methods

In general, an indirect function call might invoke any function with a
matching signature, possibly one from another package. Consequently,
analysis of indirect calls have to be very conservative.

However, non-exported interface method calls will always call a method
from the same package. This means escape analysis can optimize its
analysis somewhat, even if it doesn't know exactly which method will
be called.

See https://go.dev/issue/16001 for more details and analysis of this
optimization.
