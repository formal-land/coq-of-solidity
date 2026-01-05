From Coq Require Import Uint63.

Inductive vec8 (T: Type)
:= Vec8 (a b c d e f g h: T).
Arguments Vec8 {_}.

Definition t := vec8.

Definition map {A B: Type} (F: A -> B) (v: vec8 A)
: vec8 B
:= match v with
   | Vec8 a b c d
          e f g h => Vec8 (F a) (F b) (F c) (F d) 
                          (F e) (F f) (F g) (F h)
   end.


Definition to_list {T: Type} (v: vec8 T)
: list T
:= match v with
   | Vec8 a b c d
          e f g h => (a :: b :: c :: d :: e :: f :: g :: h :: nil)%list
   end.

Definition get {T: Type} (v: vec8 T) (i: int)
: T
:= match v with
   | Vec8 v0 v1 v2 v3 v4 v5 v6 v7 =>
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

Definition set {T: Type} (v: vec8 T) (i: int) (XX: T)
: vec8 T
:= match v with
   | Vec8 v0 v1 v2 v3 v4 v5 v6 v7 =>
         if (0 <? (i land 4))%uint63 then
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then
               Vec8 v0 v1 v2 v3 v4 v5 v6 XX
             else
               Vec8 v0 v1 v2 v3 v4 v5 XX v7
           else
             if (0 <? (i land 1))%uint63 then
               Vec8 v0 v1 v2 v3 v4 XX v6 v7
             else
               Vec8 v0 v1 v2 v3 XX v5 v6 v7
         else
           if (0 <? (i land 2))%uint63 then
             if (0 <? (i land 1))%uint63 then
               Vec8 v0 v1 v2 XX v4 v5 v6 v7
             else
               Vec8 v0 v1 XX v3 v4 v5 v6 v7
           else
             if (0 <? (i land 1))%uint63 then
               Vec8 v0 XX v2 v3 v4 v5 v6 v7
             else
               Vec8 XX v1 v2 v3 v4 v5 v6 v7
  end.