# type-inference-paper

This branch will pursue an implementation that instead of following an tree of variables structure with many cycles, uses a union find method to generate groups of
hole variables and hole structures that are constrained to be equal to be used as tree nodes; these groups can recursively depend on each other in a fixed potentially acyclic 
manner. Recursive types of type tau_1 tau_2 will naturally not be in groups with the types that compose them. However, information on group unions can be gained
by the interactions between elements within a recursive type's group. The effective left type of all recursive types must be unified. The same goes for the RHS.
Then, the type of the updated LHS and RHS groups can be recursively assessed. After they are returned, a final solution status is generated for the group. This recursive protocol
can be followed at every step of unify; upon generating a new constraint, a group can be updated and related solution statuses can also be updated. Alternatively, unify can simply
update group membership with unions and a final pass can resolve solutions (one that does not need to do DFS in excess).
<br/>
(The current plan is to work on this branch after the top-sort implementation is finished so at least one fully functioning prototype
is present before exploring potentially more elegant methods)
