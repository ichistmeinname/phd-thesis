
data Expr = Val Int | Add Expr Expr

eval :: Expr -> Int
eval (Val n)   = n
eval (Add x y) = eval x + eval y

type Stack = [Int]
type Code  = [Op]
data Op    = PUSH Int | ADD

comp :: Expr -> Code
comp (Val n)   = [PUSH n]
comp (Add x y) = comp x ++ comp y ++ [ADD]

exec :: Stack -> Code -> Stack
exec s []                    = s
exec s (PUSH n : ops)        = exec (n : s) ops
exec (m : n : s) (ADD : ops) = exec (n + m : s) ops


{-

to prove      exec s (xs ++ ys) = exec (exec s xs) ys

  exec s (xs ++ ys)
= -- Induction on xs

1) xs = []

  exec s ([] ++ ys)
= exec s ys
= exec (exec s []) ys

2) xs = z:zs

  exec s (z:zs ++ ys)
= -- case distinction on z

a) z = PUSH n

  exec s (PUSH n : zs ++ ys)
= exec (n : s) (zs ++ ys)
= -- Induction Hypothesis
  exec (exec (n : s) zs) ys
= exec (exec s (PUSH n : zs)) ys

b) z = ADD

  exec s (ADD : zs ++ ys)
= -- case distincion on s

A) s = []

  exec [] (ADD : zs ++ ys)
= undefined
= exec undefined ys
= exec (exec [] (Add : zs)) ys

B) s = st : sts

  exec (st:sts) (ADD : zs ++ ys)
= -- case distinction on sts

I) sts = nil

  exec [st] (ADD : zs ++ ys)
= undefined
= exec undefined ys
= exec (exec [st] (ADD : zs)) ys


-}
