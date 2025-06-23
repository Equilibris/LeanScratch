def ack : Nat → Nat → Nat
  | 0, n => n.succ
  | n+1, 0 => ack n 1
  | n+1, m+1 => ack n (ack n.succ m)

