From Coq Require Import Uint63.
From CoqOfSolidity Require Import Nibble UInt63.

Inductive vec16 (T: Type)
:= Vec16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf: T).
Arguments Vec16 {_}.

Local Generalizable Variable T.

Definition t := vec16.

Definition to_list `(v: vec16 T)
: list T
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
      v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 ::
      v8 :: v9 :: va :: vb :: vc :: vd :: ve :: vf :: nil
   end.

Definition fill `(x: T)
: vec16 T
:= Vec16 x x x x x x x x x x x x x x x x.

Definition fill_but_first {T: Type} (x first: T)
: vec16 T
:= Vec16 first x x x x x x x x x x x x x x x.

Definition get_by_hex `(v: vec16 T) (h: hex_digit)
: T
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
      match h with
      | x0 => v0
      | x1 => v1
      | x2 => v2
      | x3 => v3
      | x4 => v4
      | x5 => v5
      | x6 => v6
      | x7 => v7
      | x8 => v8
      | x9 => v9
      | xA => va
      | xB => vb
      | xC => vc
      | xD => vd
      | xE => ve
      | xF => vf
      end
   end.

Definition get_by_int `(v: vec16 T) (i: uint63)
: T
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
       if (0 <? (i land 8))%uint63 then
         if (0 <? (i land 4))%uint63 then
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then vf else ve
           else
             if (0 <? (i land 1))%uint63 then vd else vc
         else
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then vb else va
           else
             if (0 <? (i land 1))%uint63 then v9 else v8
       else
         if (0 <? (i land 4))%uint63 then
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then v7 else v6
           else
             if (0 <? (i land 1))%uint63 then v5 else v4
         else
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then v3 else v2
           else
             if (0 <? (i land 1))%uint63 then v1 else v0
  end.

Lemma get_by_hex_of_int `(v: vec16 T) (i: uint63):
  get_by_int v i = get_by_hex v (hex_digit_of_uint63 i).
Proof.
unfold get_by_int.
unfold hex_digit_of_uint63. unfold get_by_hex.
destruct (0 <? i land 8)%uint63;
  destruct (0 <? i land 4)%uint63;
  destruct (0 <? i land 2)%uint63;
  destruct (0 <? i land 1)%uint63; easy.
Qed.

Definition set_by_hex {T: Type} (v: vec16 T) (h: hex_digit) (XX: T)
: vec16 T
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
      match h with
      | x0 => Vec16 XX v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
      | x1 => Vec16 v0 XX v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
      | x2 => Vec16 v0 v1 XX v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
      | x3 => Vec16 v0 v1 v2 XX v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
      | x4 => Vec16 v0 v1 v2 v3 XX v5 v6 v7 v8 v9 va vb vc vd ve vf
      | x5 => Vec16 v0 v1 v2 v3 v4 XX v6 v7 v8 v9 va vb vc vd ve vf
      | x6 => Vec16 v0 v1 v2 v3 v4 v5 XX v7 v8 v9 va vb vc vd ve vf
      | x7 => Vec16 v0 v1 v2 v3 v4 v5 v6 XX v8 v9 va vb vc vd ve vf
      | x8 => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 XX v9 va vb vc vd ve vf
      | x9 => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 XX va vb vc vd ve vf
      | xA => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 XX vb vc vd ve vf
      | xB => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va XX vc vd ve vf
      | xC => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb XX vd ve vf
      | xD => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc XX ve vf
      | xE => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd XX vf
      | xF => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve XX
      end
   end.

Definition set_by_int `(v: vec16 T) (i: uint63) (XX: T)
: vec16 T
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
       if (0 <? (i land 8))%uint63 then
         if (0 <? (i land 4))%uint63 then
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve XX
             else
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd XX vf
           else
             if (0 <? (i land 1))%uint63 then 
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc XX ve vf
             else 
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb XX vd ve vf
         else
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va XX vc vd ve vf
             else 
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 XX vb vc vd ve vf
           else
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 XX va vb vc vd ve vf
             else
               Vec16 v0 v1 v2 v3 v4 v5 v6 v7 XX v9 va vb vc vd ve vf
       else
         if (0 <? (i land 4))%uint63 then
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 v1 v2 v3 v4 v5 v6 XX v8 v9 va vb vc vd ve vf 
             else
               Vec16 v0 v1 v2 v3 v4 v5 XX v7 v8 v9 va vb vc vd ve vf
           else
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 v1 v2 v3 v4 XX v6 v7 v8 v9 va vb vc vd ve vf
             else
               Vec16 v0 v1 v2 v3 XX v5 v6 v7 v8 v9 va vb vc vd ve vf
         else
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 v1 v2 XX v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
             else
               Vec16 v0 v1 XX v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
           else
             if (0 <? (i land 1))%uint63 then
               Vec16 v0 XX v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
             else
               Vec16 XX v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
  end.

Lemma set_by_hex_of_int `(v: vec16 T) (i: uint63) (new_value: T):
  set_by_int v i new_value = set_by_hex v (hex_digit_of_uint63 i) new_value.
Proof.
unfold set_by_int.
unfold hex_digit_of_uint63. unfold set_by_hex.
destruct (0 <? i land 8)%uint63;
  destruct (0 <? i land 4)%uint63;
  destruct (0 <? i land 2)%uint63;
  destruct (0 <? i land 1)%uint63; easy.
Qed.

Definition combine {T: Type} (u v: vec16 T) (h: hex_digit)
: vec16 T
:= match u with
   | Vec16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 ua ub uc ud ue uf =>
      match v with
      | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
          match h with
          | x0 => Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf
          | x1 => Vec16 uf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve
          | x2 => Vec16 ue uf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd
          | x3 => Vec16 ud ue uf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc
          | x4 => Vec16 uc ud ue uf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb
          | x5 => Vec16 ub uc ud ue uf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va
          | x6 => Vec16 ua ub uc ud ue uf v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
          | x7 => Vec16 u9 ua ub uc ud ue uf v0 v1 v2 v3 v4 v5 v6 v7 v8
          | x8 => Vec16 u8 u9 ua ub uc ud ue uf v0 v1 v2 v3 v4 v5 v6 v7
          | x9 => Vec16 u7 u8 u9 ua ub uc ud ue uf v0 v1 v2 v3 v4 v5 v6
          | xA => Vec16 u6 u7 u8 u9 ua ub uc ud ue uf v0 v1 v2 v3 v4 v5
          | xB => Vec16 u5 u6 u7 u8 u9 ua ub uc ud ue uf v0 v1 v2 v3 v4
          | xC => Vec16 u4 u5 u6 u7 u8 u9 ua ub uc ud ue uf v0 v1 v2 v3
          | xD => Vec16 u3 u4 u5 u6 u7 u8 u9 ua ub uc ud ue uf v0 v1 v2
          | xE => Vec16 u2 u3 u4 u5 u6 u7 u8 u9 ua ub uc ud ue uf v0 v1
          | xF => Vec16 u1 u2 u3 u4 u5 u6 u7 u8 u9 ua ub uc ud ue uf v0
          end
      end
   end.

Definition update_by_hex `(v: vec16 T) (h: hex_digit) (f: T -> T)
: vec16 T
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
      match h with
      | x0 => Vec16(f v0)  v1   v2   v3   v4   v5   v6   v7   v8   v9   va   vb   vc   vd   ve   vf
      | x1 => Vec16   v0(f v1)  v2   v3   v4   v5   v6   v7   v8   v9   va   vb   vc   vd   ve   vf
      | x2 => Vec16   v0   v1(f v2)  v3   v4   v5   v6   v7   v8   v9   va   vb   vc   vd   ve   vf
      | x3 => Vec16   v0   v1   v2(f v3)  v4   v5   v6   v7   v8   v9   va   vb   vc   vd   ve   vf
      | x4 => Vec16   v0   v1   v2   v3(f v4)  v5   v6   v7   v8   v9   va   vb   vc   vd   ve   vf
      | x5 => Vec16   v0   v1   v2   v3   v4(f v5)  v6   v7   v8   v9   va   vb   vc   vd   ve   vf
      | x6 => Vec16   v0   v1   v2   v3   v4   v5(f v6)  v7   v8   v9   va   vb   vc   vd   ve   vf
      | x7 => Vec16   v0   v1   v2   v3   v4   v5   v6(f v7)  v8   v9   va   vb   vc   vd   ve   vf
      | x8 => Vec16   v0   v1   v2   v3   v4   v5   v6   v7(f v8)  v9   va   vb   vc   vd   ve   vf
      | x9 => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8(f v9)  va   vb   vc   vd   ve   vf
      | xA => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8   v9(f va)  vb   vc   vd   ve   vf
      | xB => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8   v9   va(f vb)  vc   vd   ve   vf
      | xC => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8   v9   va   vb(f vc)  vd   ve   vf
      | xD => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8   v9   va   vb   vc(f vd)  ve   vf
      | xE => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8   v9   va   vb   vc   vd(f ve)  vf
      | xF => Vec16   v0   v1   v2   v3   v4   v5   v6   v7   v8   v9   va   vb   vc   vd   ve(f vf)
      end
   end.

Lemma set_via_update_by_hex `(v: vec16 T) (h: hex_digit) (new_value: T):
  set_by_hex v h new_value = update_by_hex v h (fun _ => new_value).
Proof.
now destruct h.
Qed.

Lemma get_of_update_by_hex `(v: vec16 T) (h: hex_digit) (f: T -> T):
  get_by_hex (update_by_hex v h f) h = f (get_by_hex v h).
Proof.
now destruct v, h.
Qed.

Lemma get_of_set_by_hex `(v: vec16 T) (h: hex_digit) (new_value: T):
  get_by_hex (set_by_hex v h new_value) h = new_value.
Proof.
now destruct v, h.
Qed.

Lemma get_of_update_ne_by_hex `(v: vec16 T) 
                              (h h': hex_digit)
                              (NE: h <> h')
                              (f: T -> T):
  get_by_hex (update_by_hex v h' f) h = get_by_hex v h.
Proof.
now destruct v, h, h'.
Qed.

Lemma get_of_set_ne_by_hex `(v: vec16 T) 
                           (h h': hex_digit)
                           (NE: h <> h')
                           (new_value: T):
  get_by_hex (set_by_hex v h' new_value) h = get_by_hex v h.
Proof.
rewrite set_via_update_by_hex.
now apply get_of_update_ne_by_hex.
Qed.

Definition fold_left {A B: Type} (f: A -> B -> A) (v: vec16 B) (init: A)
: A
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
      f  (f  (f  (f  (f  (f  (f  (f  (f  (f  (f  (f  (f  (f  (f  (f init
      v0) v1) v2) v3) v4) v5) v6) v7) v8) v9) va) vb) vc) vd) ve) vf
   end.

Lemma fold_left_ok {A B: Type} (f: A -> B -> A) (v: vec16 B) (init: A):
  fold_left f v init = List.fold_left f (to_list v) init.
Proof. now destruct v. Qed.

Definition fold_right {A B: Type} (f: B -> A -> A) (init: A) (v: vec16 B)
: A
:= match v with
   | Vec16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 va vb vc vd ve vf =>
       f v0 (f v1 (f v2 (f v3
      (f v4 (f v5 (f v6 (f v7
      (f v8 (f v9 (f va (f vb
      (f vc (f vd (f ve (f vf init)))))))))))))))
   end.

Lemma fold_right_ok {A B: Type} (f: B -> A -> A) (init: A) (v: vec16 B):
  fold_right f init v = List.fold_right f init (to_list v).
Proof. now destruct v. Qed.