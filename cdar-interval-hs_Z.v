From mathcomp Require Import all_ssreflect.
Require Import ZArith.
Require Import QArith.

Require Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellZInteger.
Require ExtrHaskellNatInteger.
Extraction Language Haskell.

Local Open Scope Z_scope.

Parameter hs_Z : Type.
Extract Inlined Constant hs_Z => "Prelude.Integer".

Parameter hs_Z2Z: hs_Z -> Z.
Extract Inlined Constant hs_Z2Z => "Prelude.id".

Parameter Z2hs_Z: Z -> hs_Z.
Extract Inlined Constant Z2hs_Z => "Prelude.id".

Parameter hs_eq: hs_Z -> hs_Z -> bool.
Extract Inlined Constant hs_eq => "(Prelude.==)".

Parameter hs_lt: hs_Z -> hs_Z -> bool.
Extract Inlined Constant hs_lt => "(Prelude.<)".

Parameter hs_gt: hs_Z -> hs_Z -> bool.
Extract Inlined Constant hs_gt => "(Prelude.>)".

Parameter hs_lte: hs_Z -> hs_Z -> bool.
Extract Inlined Constant hs_lte => "(Prelude.<=)".

Parameter hs_gte: hs_Z -> hs_Z -> bool.
Extract Inlined Constant hs_gte => "(Prelude.>=)".

Parameter hs_add: hs_Z -> hs_Z -> hs_Z.
Extract Inlined Constant hs_add => "(Prelude.+)".

Parameter hs_sub: hs_Z -> hs_Z -> hs_Z.
Extract Inlined Constant hs_sub => "(Prelude.-)".

Parameter hs_neg: hs_Z -> hs_Z.
Extract Inlined Constant hs_neg => "(Prelude.negate)".

Parameter hs_mul: hs_Z -> hs_Z -> hs_Z.
Extract Inlined Constant hs_mul => "(Prelude.*)".

Parameter hs_pow: hs_Z -> hs_Z -> hs_Z.
Extract Inlined Constant hs_pow => "(Prelude.^)".

Parameter hs_quotrem: hs_Z -> hs_Z -> hs_Z * hs_Z.
Extract Inlined Constant hs_quotrem => "(Prelude.quotRem)".

Parameter hs_div: hs_Z -> hs_Z -> hs_Z.
Extract Inlined Constant hs_div => "(Prelude.div)".

Parameter hs_abs: hs_Z -> hs_Z.
Extract Inlined Constant hs_abs => "(Prelude.abs)".

Notation "0" := (Z2hs_Z 0) : HS_Z_Scope.
Notation "1" := (Z2hs_Z 1) : HS_Z_Scope.
Notation "2" := (Z2hs_Z 2) : HS_Z_Scope.
Notation "3" := (Z2hs_Z 3) : HS_Z_Scope.
Notation "10" := (Z2hs_Z 10) : HS_Z_Scope.
Notation "15" := (Z2hs_Z 15) : HS_Z_Scope.
Notation "-1" := (Z2hs_Z (-1)) : HS_Z_Scope.
Notation "-10" := (Z2hs_Z (-10)) : HS_Z_Scope.
Notation "x + y" := (hs_add x y) : HS_Z_Scope.
Notation "x - y" := (hs_sub x y) : HS_Z_Scope.
Notation "- x" := (hs_neg x) : HS_Z_Scope.
Notation "x * y" := (hs_mul x y) : HS_Z_Scope.
Notation "x =? y" := (hs_eq x y) : HS_Z_Scope.
Notation "x <? y" := (hs_lt x y) : HS_Z_Scope.
Notation "x >? y" := (hs_gt x y) : HS_Z_Scope.
Notation "x <=? y" := (hs_lte x y) : HS_Z_Scope.
Notation "x >=? y" := (hs_gte x y) : HS_Z_Scope.

Delimit Scope HS_Z_Scope with HSZ.

Local Open Scope HS_Z_Scope.
(*  Approx m e s  =  [m-e , m+e]*2^s  *)

Inductive approx := Approx (m : hs_Z) (e : hs_Z) (s : hs_Z).

Definition fromNat (n : hs_Z) := Approx n 0 0.

Definition roundA s_new a :=
  match a with
  | (Approx m e s) => 
    match (hs_Z2Z (s - s_new)) with
    | Z0 | Zpos _ => a
    | Zneg k => 
        let tk := hs_pow 2 (Z2hs_Z (Zpos k)) in
        let (m_new, r) := hs_quotrem m tk in
        (* TODO: optimise more *)
        let e_pre := (hs_div (e + tk - 1) tk) in
        let e_new := 
          match (hs_Z2Z r) with
          | 0 => e_pre
          | _ => 1+e_pre
          end in
        Approx m_new e_new s_new
    end
  end.

Definition addA_exact (x1 x2 : approx) : approx :=
  match (x1,x2) with 
    | (Approx m1 e1 s1, Approx m2 e2 s2) => 
      match hs_Z2Z (s1 - s2) with
      | Z0 => Approx (m1 + m2) (e1 + e2) s1
      | Zpos k =>
          let two_pow_k := hs_pow 2 (Z2hs_Z (Zpos k)) in
          Approx (m1 * two_pow_k + m2)  (e1*two_pow_k + e2) s2
      | Zneg k =>
          let two_pow_k := hs_pow 2 (Z2hs_Z (Zpos k)) in
          Approx (m2 * two_pow_k + m1)  (e2*two_pow_k + e1) s1
      end
  end.

Definition addA (s:hs_Z) (x1 x2 : approx) : approx := roundA s (addA_exact x1 x2).

Definition mulA_exact (x1 x2 : approx) : approx :=
  match (x1,x2) with 
    | (Approx m e s, Approx n f t) => 
      let am := hs_abs m in
      let an := hs_abs n in
      let a := m * n in
      let b := m * f in
      let c := n * e in
      let d := e * f in
      let ab := hs_abs b in
      let ac := hs_abs c in
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

Definition mulA (s:hs_Z) (x1 x2 : approx) : approx := roundA s (mulA_exact x1 x2).


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

Compute logistic_map_s_n (-10) 10.

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

