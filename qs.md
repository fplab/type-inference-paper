## Questions

1. counter example for our current system:

```
contex: z:bool

λx:hole[A].(
    if z then (
        λy:int.(|e|) x             <= hole[A] ~ int      |  hole[A] consistent-less int 
    ) else (
        λy:bool.(|e|) x            <= hole[A] ~ bool     |  hole[A] consistent-less bool 
    )
)
```


2. solution:

```
[(hole[A] ~ int)]  =>  hole[A] = int
[(hole[A] ~ int); (hole[A] ~ bool);] => ill-type
[(hole[A] < int); (hole[A] < bool);] => hole[A] = bool or int
```

3. consistency

    1. ``` num ~ num ```
    2. ``` ? ~ ? ```
    3. ```
        t1 ~ t3      t2 ~ t4
        ---------------------
        t1 -> t2  ~  t3 -> t4

    4. ``` ? < t (t is all other types except THole) ```

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
