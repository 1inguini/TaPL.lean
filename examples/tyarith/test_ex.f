/* Extra Examples for testing */

if iszero succ 0 then succ succ pred 0 else succ pred succ 0;

/* evaluates, but type error */
if iszero succ 0 then succ succ pred 0 else succ pred succ 0;

/* normalize to invalid value */
if (iszero true) then 0 else (succ 0);