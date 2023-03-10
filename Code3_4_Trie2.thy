(*<*)
theory Code3_4_Trie2 
  imports Main
begin
(*>*)

datatype ('a,'v)trie = Trie  "'v option"  "('a * ('a,'v)trie)list"
value "Trie None [(a,Trie None [
                                (I,Trie None [(I,Trie (Some 1) [])]),
                                (n,Trie (Some 2) []),
                                (p,Trie None [(e,Trie (Some 3) [])])]),
                  (c,Trie None [(a,Trie None [
                                (n,Trie (Some 4) []),
                                (r,Trie (Some 5) []),
                                (t,Trie (Some 6) [])])])]"
term "a::char"(*"a" :: "char" *)
value "a::string"  (*"a":: "char list"  *)
definition "l ≡ ''a''"
value "l"
(*
definition "l2 ≡ a::char"

definition "llchar  ≡ Trie None [(''a'',Trie None [
                                (I,Trie None [(I,Trie (Some (1::nat)) [])]),
                                (n,Trie (Some 2) []),
                                (p,Trie None [(e,Trie (Some 3) [])])]),
                  (c,Trie None [(a,Trie None [
                                (n,Trie (Some 4) []),
                                (r,Trie (Some 5) []),
                                (t,Trie (Some 6) [])])])]"
*)
definition "ll = Trie None [((1::nat),Trie None [(2,Trie None [(2,Trie (Some (11::nat)) [])]),
                                                 (3,Trie (Some 12) []),
                                                 (4,Trie None [(5,Trie (Some 13) [])])
                                                ]
                           )]"
definition "ll1=Trie None [
                 (''a'',Trie None[
                         (''l'',Trie None [
                                       (''l'',Trie (Some ''all'') [])]),
                         (''n'',Trie (Some ''an'') []),
                         (''p'',Trie None [
                                       (''e'',Trie (Some ''ape'') [])])]),
                 (''c'',Trie None [
                         (''a'',Trie None [ 
                                        (''n'',Trie (Some ''can'')[]),
                                        (''r'',Trie (Some ''car'') []),
                                        (''t'',Trie (Some ''cat'') [])])])]"

value ll1 
(*"ll"
  :: "(nat, nat) trie"*)

primrec "value" :: "('a,'v)trie  ⇒ 'v option" where
"value(Trie ov al) = ov"

primrec alist :: "('a,'v)trie ⇒ ('a * ('a,'v)trie)list" where
"alist(Trie ov al) = al"

value "alist ll"
(*
"[(1, Trie None [(2, Trie None [(2, Trie (Some 1) [])]), (3, Trie (Some 2) []), (4, Trie None [(5, Trie (Some 3) [])])])]"
  :: "(nat \<times> (nat, nat) trie) list"
*)
value "value ll"
(*
"None"
  :: "nat option"
*)
primrec assoc :: "('key * 'val)list ⇒ 'key ⇒'val option" where
"assoc [] x = None" |
"assoc (p#ps) x =
   (let (a,b) = p in if a=x then Some b else assoc ps x)"
value "ll"
value " assoc (alist ll) (1::nat)"

primrec lookup :: "('a, 'v) trie ⇒ 'a list ⇒ 'v option" where
"lookup t [] = value t" |
"lookup t (a#as) = (case assoc (alist t) a of
                      None \<Rightarrow> None
                    | Some at \<Rightarrow> lookup at as)"
value "lookup ll []"
value "lookup ll [(1::nat),2,2]"

lemma [simp]: "lookup (Trie None []) as = None"
  apply (case_tac as)
  using [[simp_trace]]
apply( simp_all)
done


primrec update:: "('a,'v)trie ⇒ 'a list ⇒ 'v  ⇒ ('a,'v)trie" where
"update t []     v = Trie (Some v) (alist t)" |
"update t (a#as) v =
   (let tt = (case assoc (alist t) a of
                None ⇒ Trie None [] | Some at ⇒ at)
    in Trie (value t) ((a,update tt as v) # alist t))"
definition "testnone=Trie None []"
value " ll1"
value " assoc (alist ll1 ) (''a'')"
value "alist ll"
value "update ll1 [''a'',''n'',''m''] (''a'')"
value "update ll1 [] (''a'')"
value "update ll [1,(3::nat)] 9"
value "update ll [(2::nat),3] 2"


declare Let_def[simp] option.split[split]

theorem "\<forall>t v bs. lookup (update t as v) bs =
                    (if as=bs then Some v else lookup t bs)"
  apply(induct_tac as)
  apply auto
    apply(case_tac[!] bs)
  apply auto
done

(*<*)

(* Exercise 1 *)

primrec update1 :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie"
where
  "update1 t []     vo = Trie vo (alist t)" |
  "update1 t (a#as) vo =
     (let tt = (case assoc (alist t) a of
                  None \<Rightarrow> Trie None [] 
                | Some at \<Rightarrow> at)
      in Trie (value t) ((a, update1 tt as vo) # alist t))"

theorem [simp]: "\<forall>t v bs. lookup (update1 t as v) bs =
                    (if as = bs then v else lookup t bs)"
apply (induct_tac as, auto)
apply (case_tac[!] bs, auto)
done


(* Exercise 2 *)

primrec overwrite :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list" where
"overwrite a v [] = [(a,v)]" |
"overwrite a v (p#ps) = (if a = fst p then (a,v)#ps else p # overwrite a v ps)"

lemma [simp]: "\<forall> a v b. assoc (overwrite a v ps) b = assoc ((a,v)#ps) b"
apply (induct_tac ps, auto)
apply (case_tac[!] a)
done

primrec update2 :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie"
where
  "update2 t []     vo = Trie vo (alist t)" |
  "update2 t (a#as) vo =
     (let tt = (case assoc (alist t) a of 
                  None \<Rightarrow> Trie None []  
                | Some at \<Rightarrow> at) 
      in Trie (value t) (overwrite a (update2 tt as vo) (alist t)))" 

theorem "\<forall>t v bs. lookup (update2 t as vo) bs =
                    (if as = bs then vo else lookup t bs)"
apply (induct_tac as, auto)
apply (case_tac[!] bs, auto)
done


(* Exercise 3 *)
datatype ('a,dead 'v) triem = Triem  "'v option" "'a \<Rightarrow> ('a,'v) triem option"

primrec valuem :: "('a, 'v) triem \<Rightarrow> 'v option" where
"valuem (Triem ov m) = ov"

primrec mapping :: "('a,'v) triem \<Rightarrow> 'a \<Rightarrow> ('a, 'v) triem option" where
"mapping (Triem ov m) = m"

primrec lookupm :: "('a,'v) triem \<Rightarrow> 'a list \<Rightarrow> 'v option" where
  "lookupm t [] = valuem t" |
  "lookupm t (a#as) = (case mapping t a of
                        None \<Rightarrow> None
                      | Some at \<Rightarrow> lookupm at as)"

lemma [simp]: "lookupm (Triem None  (\<lambda>c. None)) as = None"
apply (case_tac as, simp_all)
done

primrec updatem :: "('a,'v)triem \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a,'v)triem" where
  "updatem t []     v = Triem (Some v) (mapping t)" |
  "updatem t (a#as) v =
     (let tt = (case mapping t a of
                  None \<Rightarrow> Triem None (\<lambda>c. None) 
                | Some at \<Rightarrow> at)
      in Triem (valuem t) 
              (\<lambda>c. if c = a then Some (updatem tt as v) else mapping t c))"

theorem "\<forall>t v bs. lookupm (updatem t as v) bs = 
                    (if as = bs then Some v else lookupm t bs)"
apply (induct_tac as, auto)
apply (case_tac[!] bs, auto)
done

end
(*>*)
