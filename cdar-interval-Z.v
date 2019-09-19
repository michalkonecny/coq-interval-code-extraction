From mathcomp Require Import all_ssreflect.
Require Import BinNums.
Require Import ZArith.
Require Import QArith.

Local Open Scope Z_scope.

(*  Approx m e s  =  [m-e , m+e]*2^s  *)

Inductive approx := Approx (m : Z) (e : Z) (s : Z).

Definition fromNat (n : Z) := Approx n 0 0.

Definition roundA s_new a :=
  match a with
  | (Approx m e s) => 
    match s - s_new with
    | Z0 | Zpos _ => a
    | Zneg k => 
        let tk := Z.pow_pos 2 k in
        let (m_new, r) := Z.quotrem m tk in
        (* TODO: optimise more *)
        let e_pre := (Z.div (e + tk - 1) tk) in
        let e_new := 
          match r with
          | 0 => e_pre
          | _ => 1+e_pre
          end in
        Approx m_new e_new s_new
    end
  end.

Compute roundA 2 (Approx 3 0 0).

Definition addA_exact (x1 x2 : approx) : approx :=
  match (x1,x2) with 
    | (Approx m1 e1 s1, Approx m2 e2 s2) => 
      match s1 - s2 with
      | Z0 => Approx (m1 + m2) (e1 + e2) s1
      | Zpos k =>
          let two_pow_k := Z.pow_pos 2 k in
          Approx (m1 * two_pow_k + m2)  (e1*two_pow_k + e2) s2
      | Zneg k =>
          let two_pow_k := Z.pow_pos 2 k in
          Approx (m2 * two_pow_k + m1)  (e2*two_pow_k + e1) s1
      end
  end.

Definition addA (s:Z) (x1 x2 : approx) : approx := roundA s (addA_exact x1 x2).

Definition mulA_exact (x1 x2 : approx) : approx :=
  match (x1,x2) with 
    | (Approx m e s, Approx n f t) => 
      let am := Z.abs m in
      let an := Z.abs n in
      let a := m * n in
      let b := m * f in
      let c := n * e in
      let d := e * f in
      let ab := Z.abs b in
      let ac := Z.abs c in
      let u := s+t in
      if (am >=? e) && (an >=? f) && (a >? 0)  then Approx (a+d) (ab+ac) u
      else if (am >=? e) && (an >=? f) && (a <? 0) then Approx (a-d) (ab+ac) u
      else if (am <? e) && (n >=? f)            then Approx (a+b) (ac+d) u
      else if (am <? e) && (-n >=? f)           then Approx (a-b) (ac+d) u
      else if (m >=? e) && (an <? f)            then Approx (a+c) (ab+d) u
      else if (-m >=? e) && (an <? f)           then Approx (a-c) (ab+d) u
      else if  a =? 0                      then Approx (0) (ab+ac+d) u
      else if (am <? e) && (an <? f) && (a >? 0) && (ab >? ac)  then Approx (a+ac) (ab+d) u
      else if (am <? e) && (an <? f) && (a >? 0) && (ab <=? ac) then Approx (a+ab) (ac+d) u
      else if (am <? e) && (an <? f) && (a <? 0) && (ab >? ac)  then Approx (a-ac) (ab+d) u
      else if (am <? e) && (an <? f) && (a <? 0) && (ab <=? ac) then Approx (a-ab) (ac+d) u
      else Approx 0 0 0 (*  this should never happen *)
  end.

Definition mulA (s:Z) (x1 x2 : approx) : approx := roundA s (mulA_exact x1 x2).


(*
    (Approx mb1 m e s) * (Approx mb2 n f t)
        | am >= e && an >= f && a > 0           = Approx (a+d) (ab+ac) u
        | am >= e && an >= f && a < 0           = Approx (a-d) (ab+ac) u
        | am < e && n >= f                      = Approx (a+b) (ac+d) u
        | am < e && -n >= f                     = Approx (a-b) (ac+d) u
        | m >= e && an < f                      = Approx (a+c) (ab+d) u
        | -m >= e && an < f                     = Approx (a-c) (ab+d) u
        | a == 0                                = Approx (0) (ab+ac+d) u
        | am < e && an < f && a > 0 && ab > ac  = Approx (a+ac) (ab+d) u
        | am < e && an < f && a > 0 && ab <= ac = Approx (a+ab) (ac+d) u
        | am < e && an < f && a < 0 && ab > ac  = Approx (a-ac) (ab+d) u
        | am < e && an < f && a < 0 && ab <= ac = Approx (a-ab) (ac+d) u
 
*)

Require Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellZInteger.
Require ExtrHaskellNatInteger.
Extraction Language Haskell.
Extract Inlined Constant Z.abs => "(Prelude.abs)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.opp => "(Prelude.negate)".
Extract Inlined Constant Z.succ => "(Prelude.succ)".
Extract Inlined Constant Z.pow_pos => "(Prelude.^)".
Extract Inlined Constant Z.quotrem => "(Prelude.quotRem)".

Definition test_mul := mulA (-10) (Approx 2 0 0) (Approx 1 1 (-1)).

Definition test_add := addA (-10) (Approx 1 0 0) (Approx 1 1 (-1)).

Fixpoint logistic_map (s:Z) (x0:approx) (r:approx) (n:nat) :=
  match n with
  | 0%nat => x0
  | n'.+1 => 
    let xn' := logistic_map s x0 r n' in
      mulA s r (mulA s xn' (addA s (Approx 1 0 0) (mulA s (Approx (-1) 0 0) xn') ))
  end.

Definition logistic_map_s_n s n := 
  let x0 := Approx 1 0 (-1) in
  let r := Approx 15 0 (-2) in
  logistic_map s x0 r n.

Compute logistic_map_s_n (-20) 10.

Extraction "logistic_map_s_n" logistic_map_s_n.


(* 
Compute (addA (Approx 1 0 0) (Approx 1 1 (-1))).
 *)


(* Logistic map:  x_{n+1} = r*x_n*(1-x_n)  *)

(*

Definition fromRat (s : Z) (r : Q) := 
  let r_scaled := (r * ((2#1)^s))%Q in
  let r_scaled_rounded := Qceiling (r_scaled) in 
  let s_num := Qnum r_scaled in
  let s_den := Qden r_scaled in
  Approx m e s.

Inductive approx := Bottom | Approx (mb : Z) (m : Z) (e : Z) (s : Z).

Definition approx_correct (a : approx) : Prop := 
  match a with
    Bottom => true
  | Approx mb m e s => 
      (mb > Z0) /\ (e >= Z0) /\ (m <= 2^mb) /\ ((Z0-m) <= 2^mb)
  end.

Definition enforceMB (a : approx) :=
  match a with
    Bottom => Bottom
    Approx mb m e s => Approx mb 

*)

