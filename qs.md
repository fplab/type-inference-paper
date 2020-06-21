## Questions

1. counter example for our current system:

```
context: z:bool

?
λx.(
    if z then (
        (λy:int.(|e|)) x             <= hole[A] ~ int      |  hole[A] consistent-less int 
    ) else (
        (λy:bool.(|e|)) x            <= hole[A] ~ bool     |  hole[A] consistent-less bool 
    )
) 
```

type id_solution = 
| Solved of HTyp.t
| Unsolved of list(HTyp.t) (* suggestions based on partial solutions *)

type Solution.t = list((id, id_solution))

unification : Constraints.t -> Solutions.t

2. 
    subs:   id*Typ.t list  [("A", num); ("B", bool)]   ==>  
            id*op*(Typ.t list) list [("A", <, [num,bool]); ("B", ~, [bool])];

    cons:   Typ.t*Typ.t list ==> Typ.t*op*Typ.t

    1. modification of unification alg:
        - change constraints gathering
        
        - change unify function.

            in unify:

            ```
            match cons with
            | (x, y) :: xs ->
                let subs_xs =  unify xs 
                in  (
                    match unify_one (apply subs_xs x) (apply subs_xs y) with
                    | ("A", <, t) -> 
                        if (subs_xs.contain "A" && op == <), subs_xs["A"].append(t)
                        if (subs_xs.contain "A" && op == ~), ignore
                        esle add ("A", <, t) into subs_xs
                    | ("A", ~, t) -> 
                        if (subs_xs.contain "A" && op == <), subs_xs["A"] = ("A", ~, t)
                        if (subs_xs.contain "A" && op == ~), error
                        esle add ("A", ~, t) into subs_xs
                )
            ```

            in unify_one:
            ```
            (THole "A", <, t) => ("A", <, t);
            (THole "A", ~, t) => ("A", ~, t);
            ```
            
            in apply:
            only applys (_, ~, _), not (_, <, _)

    2. solution:

        ```
        cons: [(THole "A", ~, int)]  
        subs: [("A", ~, int)]  
        ==> hole[A] = int

        cons: [(THole "A", ~, int); (THole "A", ~, bool);]
        subs: None
        ==> ill-type

        cons: [(THole "A", <, int); (THole "A", <, bool);] 
        subs: [("A", <, [int, bool]);]
        ==> hole[A] = int or bool

        cons: [(THole "A", <, bool); (THole "A", ~, int);]           ==> int ~ bool error
        subs: [("A", ~, int);]
        ==>  hole[A] = int
        ```


3. consistency

    1. ``` num ~ num ```
    2. ``` hole ~ hole ```
    3. ```
        t1 ~ t3      t2 ~ t4
        ---------------------
        t1 -> t2  ~  t3 -> t4

    4. ```hole ~ t or hole < t ``` (t is all other types except THole) *

    5. 
        ```
        t1 < t3      t2 < t4
        ---------------------
        t1 -> t2  <  t3 -> t4
        ```
        ```
        t1 < t3      t2 ~ t4
        ---------------------
        t1 -> t2  <  t3 -> t4
        ```
        ```
        t1 ~ t3      t2 < t4
        ---------------------
        t1 -> t2  <  t3 -> t4
        ```

4. trace back errors