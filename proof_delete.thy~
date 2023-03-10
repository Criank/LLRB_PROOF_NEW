theory proof_delete
imports 
  proof_insert
begin

subsection \<open>functional implementation of llrb's delete operation\<close>

fun rightredR:: "'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"rightredR (B t1 a t2) b (R t3 c t4) = R (R (B t1 a t2) b t3) c t4"|
"rightredR Leaf a (R t1 b t2) = R (R Leaf a t1) b t2"|
"rightredR t1 a t2 = R t1 a t2"

fun baldL :: "'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"baldL (R t1 a t2) b t3 = rightredR (B t1 a t2) b t3" |
"baldL t1 a (B t2 b t3) = baliR t1 a (R t2 b t3)" |
"baldL t1 a (R (B t2 b t3) c t4) = rightredR (rightredB t1 a t2) b (baliR t3 c (paint Red t4))" |
"baldL t1 a t2 = rightredR t1 a t2"

fun baldR :: "'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"baldR t1 a (R t2 b t3) = R t1 a (B t2 b t3)" |
"baldR (B t1 a t2) b t3 = baliL (R t1 a t2) b t3" |
"baldR (R t1 a (B t2 b t3)) c t4 = R (baliL (paint Red t1) a t2) b (B t3 c t4)" |
"baldR t1 a t2 = rightredR t1 a t2"

fun split_min :: "'a llrb \<Rightarrow> 'a \<times> 'a llrb" where
"split_min (Node l (a, _) r) =
  (if l = Leaf then (a,r)
   else let (x,l') = split_min l
        in (x, if color l = Black then (baldL l' a r) else (rightredR l' a r)))"

fun del :: "'a::linorder \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"del x Leaf = Leaf" |
"del x (Node l (a, _) r) =
  (case cmp x a of
     LT \<Rightarrow> let l' = del x l in if l \<noteq> Leaf \<and> color l = Black
           then baldL l' a r else (rightredR l' a r) |
     GT \<Rightarrow> let r' = del x r in if r \<noteq> Leaf \<and> color r = Black
           then baldR l a r' else R l a r' |
     EQ \<Rightarrow> if r = Leaf then l else let (a',r') = split_min r in
           if color r = Black then baldR l a' r' else (rightredR l a' r'))"

definition delete :: "'a::linorder \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"delete x t = paint Black (del x t)"

subsection \<open>locale implementation\<close>

locale llrb_op =
fixes pre_invl::"('a::linorder) llrb \<Rightarrow>'a llrb \<Rightarrow>'a \<Rightarrow> 'a llrb  \<Rightarrow> 'a llrb"
  and pre_invr::"'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb  \<Rightarrow>'a llrb \<Rightarrow> 'a llrb"
  and pre_invsplit::"'a llrb \<Rightarrow>'a \<Rightarrow> 'a llrb  \<Rightarrow> 'a llrb"
begin

fun del'::"'a::linorder  \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where 
   "del' x Leaf = Leaf"|
   "del' x (Node l (a, _) r) = (case cmp x a of 
              LT \<Rightarrow> pre_invl (del' x l) l a r|
              GT \<Rightarrow> pre_invr l a r (del' x r)|
              EQ \<Rightarrow> pre_invsplit l a r)"

fun ins' :: "'a::linorder \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
   "ins' x Leaf = R Leaf x Leaf" |
   "ins' x (B l a r) = (case cmp x a of 
              LT \<Rightarrow> pre_invl (ins' x l) l a r |
              GT \<Rightarrow> pre_invr l a r (ins' x r) |
              EQ \<Rightarrow> B l a r)" |
   "ins' x (R l a r) = (case cmp x a of 
              LT \<Rightarrow> R (ins x l) a r |
              GT \<Rightarrow> R l a (ins x r) |
              EQ \<Rightarrow> R l a r)"
end

locale llrb_delete 
begin
definition pre_invl'::"('a::linorder) llrb \<Rightarrow>'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb "
  where "pre_invl' l' l a r = ( if l \<noteq> Leaf \<and> color l = Black
                                then baldL l' a r else rightredR l' a r)"

definition pre_invr'::"('a ::linorder) llrb \<Rightarrow>'a \<Rightarrow> 'a llrb \<Rightarrow>'a llrb \<Rightarrow> 'a llrb "
  where "pre_invr' l a r r' = ( if r \<noteq> Leaf \<and> color r = Black
                                then baldR l a r' else R l a r')"

definition pre_invsplit'::" 'a llrb \<Rightarrow>'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb"
  where "pre_invsplit' l a r = (if r = Leaf then l else (let (a', r') = split_min r in
                                if color r = Black then baldR l a' r' else rightredR l a' r'))"

interpretation llrb_op pre_invl' pre_invr' pre_invsplit'
done

term "del'" 
thm "del'.simps"

definition delete' :: "'a::linorder \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"delete' x t = paint Black (del' x t)"

lemma locdel_eq_del:"del' x t = del x t"
  apply(induct t)
  apply simp
  apply(case_tac "x2")
  apply (simp only: del'.simps del.simps)
  by (simp add: pre_invl'_def pre_invr'_def pre_invsplit'_def)
end

locale llrb_insert
begin
fun baliL' :: "('a ::linorder) llrb \<Rightarrow>'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"baliL' (R t1 a (R t2 b t3)) _ c t4 = R (B t1 a t2) b (rightredB t3 c t4)" |
"baliL' (R (R t1 a t2) b t3) _ c t4 = R (B t1 a t2) b (rightredB t3 c t4)" |
"baliL' t1 _ a t2 = rightredB t1 a t2"

fun baliR' :: "('a ::linorder) llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb \<Rightarrow>'a llrb" where
"baliR' t1 a _ (R t2 b (R t3 c t4)) = R (rightredB t1 a t2) b (B t3 c t4)" |
"baliR' t1 a _ (R (R t2 b t3) c t4) = R (B t1 a t2) b (rightredB t3 c t4)" |
"baliR' t1 a _ t2 = rightredB t1 a t2"  

interpretation llrb_op baliL' baliR'
done

term "ins'" 
thm "ins'.simps"

lemma baliL'_eq_baliL:"baliL' l' l a r = baliL l' a r"
  apply(case_tac "l'")
  apply simp+
  apply(case_tac "x22")
  apply(case_tac "b")
  defer
  apply simp
  apply (case_tac"x21")
  apply (case_tac"x23")
  apply simp+
  apply(case_tac"x22a")
  apply(case_tac"ba")
  defer
  apply simp+
  apply(case_tac"x22a")
  apply(case_tac"ba")
  apply (case_tac"x23")
  apply simp+
  apply(case_tac"x22b")
  apply(case_tac"bb")
  apply simp+
  apply (case_tac"x23")
  apply simp+
  apply(case_tac"x22b")
  apply(case_tac"bb")
  apply simp+
  done

lemma baliR'_eq_baliR:"baliR' l a r r' = baliR l a r'"
  apply(case_tac "r'")
  apply simp+
  apply(case_tac "x22")
  apply(case_tac "b")
  defer
  apply simp
  apply (case_tac"x21")
  apply (case_tac"x23")
  apply simp+
  apply(case_tac"x22a")
  apply(case_tac"ba")
  defer
  apply simp+
  apply(case_tac"x22a")
  apply(case_tac"ba")
  apply (case_tac"x23")
  apply simp+
  apply(case_tac"x22b")
  apply(case_tac"bb")
  apply simp+
  apply (case_tac"x23")
  apply simp+
  apply(case_tac"x22b")
  apply(case_tac"bb")
  apply simp+
  done

lemma locins_eq_ins:"ins' x t = ins x t"
  apply(induct t)
  apply simp
  apply(case_tac "x2")
  apply(case_tac "b")
  apply (simp only: ins'.simps ins.simps)
  by (metis ins'.simps(2) ins.simps(2) baliL'_eq_baliL baliR'_eq_baliR)

end

subsection \<open>proof of bst_delete\<close>

lemma colorbr:
  "(B l a r = R l a r) \<Longrightarrow> false"
  by simp

lemma bst_rightredR:
  "inorder (rightredR l a r) = inorder l @ a # inorder r"
  by(cases "(l, a, r)" rule: rightredR.cases) auto

lemma bst_baldL:
  "inorder(baldL l a r) = inorder l @ a # inorder r"
  by(cases "(l,a,r)" rule: baldL.cases)
  (auto simp: bst_baliR bst_paint bst_rightredR bst_rightredB)

lemma bst_baldR:
  "inorder(baldR l a r) = inorder l @ a # inorder r"
  by(cases "(l,a,r)" rule: baldR.cases)
  (auto simp: bst_baliL bst_paint bst_rightredR)

lemma bst_split_min: "split_min t = (x,t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x # inorder t' = inorder t"
  by(induction t arbitrary: t' rule: split_min.induct)
  (auto simp: sorted_lems bst_baldL bst_rightredR split: prod.splits if_splits)

lemma bst_del:
  "sorted(inorder t) \<Longrightarrow> inorder(del x t) = del_list x (inorder t)"
  apply(induction t) 
  apply(auto simp: del_list_simps bst_rightredR bst_split_min split: prod.splits)
  apply (simp add: bst_baldR)
  apply (smt (verit, ccfv_SIG) inorder.simps(1) bst_rightredR bst_baldL)
  apply (simp add: bst_split_min bst_baldR)
  apply (smt (verit, best) bst_rightredR bst_baldL)
  by(smt (verit, best) bst_rightredR bst_baldL)

theorem bst_delete: 
  "sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
  by(auto simp: delete_def bst_del bst_paint)

subsection \<open>proof of invh_delete\<close>

lemma bheight_false: " (bheight r - Suc 0 = bheight r \<and> r \<noteq> Leaf \<and> color r = Black) = False"
  by(cases r rule: search_tree2_cases) auto

lemma neq_LeafD: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x c r. t = Node l (x,c) r"
  by(cases t rule: search_tree2_cases) auto

lemma bheight_paint_Red:
  "color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
  by (cases t) auto

lemma invh_rightredR:
  "\<lbrakk> invh l;  invh r;  bheight l  = bheight r \<rbrakk> \<Longrightarrow> invh (rightredR l a r) \<and> bheight (rightredR l a r) = bheight r"
  apply (induct l a r rule: rightredR.induct)
  apply (smt (verit) rightredR.simps(1) Suc_eq_plus1 bheight.simps(2) bheight_paint_Red  diff_Suc_1 color.simps(2) invh.simps(2) paint.simps(2))
  by simp+

lemma invh_baldL:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  invc r \<rbrakk> \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
  by(induct l a r rule: baldL.induct)
  (auto simp: invh_baliR invh_paint bheight_baliR bheight_paint_Red invh_rightredR invh_bheight_rightredB)
                                                   
lemma invh_baldR:
  "\<lbrakk> invh l;  invh r;  bheight l  = bheight r + 1;  invc l \<rbrakk> \<Longrightarrow> invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l"
  by(induct l a r rule: baldR.induct)
  (auto simp: invh_baliL invh_paint bheight_baliL bheight_paint_Red)

lemma invh_split_min: 
  "\<lbrakk>split_min t = (x,t'); t \<noteq> Leaf; invh t; invc t \<rbrakk> \<Longrightarrow>
    invh t' \<and> (color t = Red \<longrightarrow> bheight t' = bheight t) \<and>(color t = Black \<longrightarrow> bheight t' = bheight t - 1)"
  apply(induction t arbitrary: x t' rule: split_min.induct)
  apply(auto split: if_splits prod.splits)
  apply(auto dest!: neq_LeafD)
  by(auto simp: invh_baldR invh_baldL invh_baliR invh_rightredR) 

lemma invh_del_f1:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow>
   color r = Black \<Longrightarrow> x < a \<Longrightarrow> invh (del x l) \<Longrightarrow> color l = Black \<Longrightarrow>
   bheight (del x l) = bheight r - Suc 0 \<Longrightarrow>
   invh (let l' = del x l in if l \<noteq> \<langle>\<rangle> then baldL l' a r else rightredR l' a r)"
   apply(case_tac "l= Leaf")
   apply auto
   apply (simp add: invh_rightredR)
   by(metis Suc_eq_plus1 Suc_pred bheight_false diff_0_eq_0 invh_baldL not_gr_zero)

lemma invh_del_f2:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow>
   color r = Black \<Longrightarrow> x < a \<Longrightarrow> invh (del x l) \<Longrightarrow> bheight r - Suc 0 = bheight r \<Longrightarrow>
   bheight (del x l) = bheight r \<Longrightarrow>
   invh (let l' = del x l in if l \<noteq> \<langle>\<rangle> \<and> color l = Black then baldL l' a r else rightredR l' a r)"
   apply(case_tac "l= Leaf")
   apply auto
   apply (simp add: invh_rightredR)
   by (metis (mono_tags, lifting) bheight_false invh_rightredR)

lemma invh_del_f3:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow>
   color r = Black \<Longrightarrow> x < a \<Longrightarrow> invh (del x l) \<Longrightarrow> color l = Black \<Longrightarrow>
   bheight (del x l) = bheight r - Suc 0 \<Longrightarrow>
   bheight (let l' = del x l in if l \<noteq> \<langle>\<rangle> then baldL l' a r else rightredR l' a r) = bheight r"
   apply(case_tac "l= Leaf")
   apply auto
   apply (simp add: invh_rightredR)
   by(metis Suc_eq_plus1 Suc_pred bheight_false diff_less_Suc gr_implies_not_zero gr_zeroI less_SucE invh_baldL)

lemma invh_del_f4:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow>
   color r = Black \<Longrightarrow> x < a \<Longrightarrow>invh (del x l) \<Longrightarrow> bheight r - Suc 0 = bheight r \<Longrightarrow>
   bheight (del x l) = bheight r \<Longrightarrow>
   bheight (let l' = del x l in if l \<noteq> \<langle>\<rangle> \<and> color l = Black then baldL l' a r else rightredR l' a r) = bheight r"
   apply(case_tac "l= Leaf")
   apply auto
   apply (simp add: invh_rightredR)
   by(metis (mono_tags, lifting) bheight_false invh_rightredR)

lemma invh_del_f5:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow>
   color r = Black \<Longrightarrow> a < x \<Longrightarrow> invh (del x r) \<Longrightarrow> bheight (del x r) = bheight r - Suc 0 \<Longrightarrow>
   invh (let r' = del x r in if r \<noteq> \<langle>\<rangle> then baldR l a r' else R l a r')"
   apply(case_tac "r= Leaf")
   apply auto
   by(metis Suc_eq_plus1 Suc_pred bheight_false diff_0_eq_0 invh_baldR not_gr_zero)

lemma invh_del_f6:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow>  color r = Black \<Longrightarrow> a < x \<Longrightarrow>
   invh (del x r) \<Longrightarrow> bheight (del x r) = bheight r - Suc 0 \<Longrightarrow>
   bheight (let r' = del x r in if r \<noteq> \<langle>\<rangle> then baldR l a r' else R l a r') = bheight r"
   apply(case_tac "r= Leaf")
   apply auto
   by(metis Suc_eq_plus1 Suc_pred bheight_false diff_0_eq_0 invh_baldR not_gr_zero)

lemma invh_del_f7:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color l = Red \<Longrightarrow> a < x \<Longrightarrow>
   invh (del x r) \<Longrightarrow> bheight r - Suc 0 = bheight r \<Longrightarrow> bheight (del x r) = bheight r \<Longrightarrow>
   invh (let r' = del x r in if r \<noteq> \<langle>\<rangle> \<and> color r = Black then baldR l a r' else R l a r')"
   apply(case_tac "r= Leaf")
   apply auto
   using bheight_false by fastforce

lemma invh_del_f8:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color l = Red \<Longrightarrow> a < x \<Longrightarrow>
   invh (del x r) \<Longrightarrow> bheight r - Suc 0 = bheight r \<Longrightarrow> bheight (del x r) = bheight r \<Longrightarrow>
   bheight (let r' = del x r in if r \<noteq> \<langle>\<rangle> \<and> color r = Black then baldR l a r' else R l a r') = bheight r"
   apply(case_tac "r= Leaf")
   apply auto
   using bheight_false by fastforce

lemma invh_del: "\<lbrakk>invh t; invc t\<rbrakk> \<Longrightarrow> invh (del x t) \<and>
                 (color t = Red \<longrightarrow> bheight (del x t) = bheight t) \<and>
                 (color t = Black \<longrightarrow> bheight (del x t) = bheight t - 1)"
  apply(induction x t rule: del.induct)
  apply(auto simp: invh_baldR invh_baldL invc2I invh_rightredR
            dest!: invh_split_min 
             dest: neq_LeafD
           split!: prod.splits if_splits)
  by(auto simp: invh_del_f1 invh_del_f2 invh_del_f3 invh_del_f4  invh_del_f5 
                   invh_del_f6 invh_del_f7 invh_del_f8)

theorem invh_delete: "llrb t \<Longrightarrow> invh (delete x t)"
  by (simp add: delete_def invh_del invh_paint llrb_def)

subsection \<open>proof of invc_delete\<close>

lemma color_rightredR:"color (rightredR l a r) = Red"
  apply (induct l a r rule: rightredR.induct)
  by auto

lemma invc2_rightredR:"invc l \<Longrightarrow> invc r \<Longrightarrow> invc2 (rightredR l a r)"
  apply (induct l a r rule: rightredR.induct)
  by auto

lemma invc_rightredR:"invc l \<Longrightarrow> invc r \<Longrightarrow> color r = Black \<Longrightarrow> color l = Black \<Longrightarrow> invc (rightredR l a r)"
  apply (induct l a r rule: rightredR.induct)
  by auto

lemma invc_baliR: "\<lbrakk>invc l; invc2 r\<rbrakk> \<Longrightarrow> invc (baliR l a r)" 
  apply (induct l a r rule: baliR.induct)
  by(auto simp: invc_rightredB color_rightredB)

lemma invc_baliL: "\<lbrakk>invc2 l; invc r\<rbrakk> \<Longrightarrow> invc (baliL l a r)" 
  apply (induct l a r rule: baliL.induct)
  by(auto simp: invc_rightredB color_rightredB)

lemma inv_baliR: "\<lbrakk> invh l; invh r; invc l; invc2 r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> invc (baliR l a r) \<and> invh (baliR l a r) \<and> bheight (baliR l a r) = Suc (bheight l)"
  apply (induct l a r rule: baliR.induct)
  apply (auto simp: color_rightredB invc_rightredB bheight_rightredB invh_rightredB)
  done

lemma inv_baliL: "\<lbrakk> invh l; invh r; invc2 l; invc r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> invc (baliL l a r) \<and> invh (baliL l a r) \<and> bheight (baliL l a r) = Suc (bheight l)"
  apply (induct l a r rule: baliL.induct)
  apply (auto simp: color_rightredB invc_rightredB bheight_rightredB invh_rightredB)
  done

lemma invc_baldR:
  "\<lbrakk> invh l;  invh r;  bheight l = bheight r + 1; invc l; invc2 r \<rbrakk>
   \<Longrightarrow> invc2 (baldR l a r) \<and> (color l = Black \<longrightarrow> invc (baldR l a r))"
  apply (induct l a r rule: baldR.induct)
  by(auto simp: inv_baliL invh_paint bheight_paint_Red paint2 invc2I)

lemma invc_baldL:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r; invc2 l; invc r \<rbrakk>
   \<Longrightarrow>  invc2 (baldL l a r) \<and> (color r = Black \<longrightarrow> invc (baldL l a r))"
  apply (induct l a r rule: baldL.induct)
  apply(auto simp: inv_baliR invh_paint bheight_paint_Red paint2 invc2I invc2_rightredR invc_rightredR)
  by (simp add: invc2I invc2_rightredR invc_rightredB invc_baliR paint2)+

lemma invc_baldL1: "\<lbrakk>invc2 l; invc r; color r = Black\<rbrakk> \<Longrightarrow> invc (baldL l a r)"
  apply(induct l a r rule: baldL.induct)
  by(auto simp: invc_baliR invc_rightredR)

lemma invc2_baldL: "\<lbrakk> invc2 l; invc r \<rbrakk> \<Longrightarrow> invc2 (baldL l a r)"
  apply (induct l a r rule: baldL.induct) 
  apply(auto simp: invc_baliR invc2I invc2_rightredR)
  by (simp add: invc2I invc2_rightredR invc_rightredB invc_baliR paint2)+

lemma invc_baldR1: "\<lbrakk>invc l; invc2 r; color l = Black\<rbrakk> \<Longrightarrow> invc (baldR l a r)"
  by(induct l a r rule: baldR.induct) (simp_all add: invc_baliL)

lemma invc2_baldR: "\<lbrakk> invc l; invc2 r \<rbrakk> \<Longrightarrow>invc2 (baldR l a r)"
  by(induct l a r rule: baldR.induct) (auto simp: invc_baliL paint2 invc2I)

lemma invc_split_min: "\<lbrakk> split_min t = (x,t'); t \<noteq> Leaf; invh t; invc t \<rbrakk> \<Longrightarrow>
   (color t = Red \<longrightarrow> invc t') \<and> (color t = Black \<longrightarrow>  invc2 t')"
  apply(induction t arbitrary: x t' rule: split_min.induct)
  apply(auto split: if_splits prod.splits)
  apply(auto dest!: neq_LeafD)
  by(auto simp: invc_baldR invc_baldL invc2I invc2_rightredR invc_baldL1)

lemma invc_del_f1:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color r = Black \<Longrightarrow> x < a \<Longrightarrow> color l = Black \<Longrightarrow>
   invc2 (del x l) \<Longrightarrow> invc2 (let l' = del x l in if l \<noteq> \<langle>\<rangle> then baldL l' a r else rightredR l' a r)"
   apply(case_tac "l = Leaf")
   apply auto
   apply (simp add: invc2_rightredR)
   by(simp add: invc2_baldL)

lemma invc_del_f2:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color r = Black \<Longrightarrow> x < a \<Longrightarrow>
   invc (del x l) \<Longrightarrow> invc2 (let l' = del x l in if l \<noteq> \<langle>\<rangle> \<and> color l = Black then baldL l' a r else rightredR l' a r)"
   apply(case_tac "l = Leaf")
   apply auto
   apply (simp add: invc2_rightredR)
   by (smt (verit, best) invc2I invc2_rightredR invc_del_f1)

lemma invc_del_f3: 
  "invc2 (del x r) \<Longrightarrow> bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color r = Black \<Longrightarrow>
   a < x \<Longrightarrow> invc2 (let r' = del x r in if r \<noteq> \<langle>\<rangle> then baldR l a r' else R l a r')"
   apply(case_tac "r = Leaf")
   apply auto
   by(metis color.simps(2) add_diff_cancel_right' bheight.elims invh_del invc_baldR)

lemma invc_del_f4:
  "bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color l = Red \<Longrightarrow> a < x \<Longrightarrow>
   invc (del x r) \<Longrightarrow> invc2 (let r' = del x r in if r \<noteq> \<langle>\<rangle> \<and> color r = Black then baldR l a r' else R l a r')"
   apply(case_tac "r = Leaf")
   apply auto
   by(metis (full_types) color.distinct(1) invc.simps(2) invc2I invc2_baldR paint.simps(2))

lemma invc_del_f5:
  "invc2 (del x l) \<Longrightarrow> bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color l = Black \<Longrightarrow>
   color r = Black \<Longrightarrow> x < a \<Longrightarrow> invc (let l' = del x l in if l \<noteq> \<langle>\<rangle> then baldL l' a r else rightredR l' a r)"
   apply(case_tac "l = Leaf")
   apply auto
   apply (simp add: invc_rightredR)
   using invc_baldL1 by fastforce

lemma  invc_del_f6:
  "invc2 (del x r) \<Longrightarrow> bheight l = bheight r \<Longrightarrow> invh l \<Longrightarrow> invh r \<Longrightarrow> invc l \<Longrightarrow> invc r \<Longrightarrow> color l = Black \<Longrightarrow>
   color r = Black \<Longrightarrow> a < x \<Longrightarrow> invc (let r' = del x r in if r \<noteq> \<langle>\<rangle> then baldR l a r' else R l a r')"
   apply(case_tac "r = Leaf")
   apply auto
   by(meson invc_baldR1)

lemma invc_del: 
  "\<lbrakk> invh t; invc t \<rbrakk> \<Longrightarrow> (color t = Red \<longrightarrow> invc (del x t)) \<and> (color t = Black \<longrightarrow>  invc2 (del x t))"
  apply(induction x t rule: del.induct)
  apply(auto simp: invc_baldR invc2_baldR invc_baldR1 invc_baldL invc2_baldL invc_baldL1 invc2I invc2_rightredR 
            dest!: invc_split_min 
             dest: neq_LeafD
           split!: prod.splits if_splits)
  by(auto simp: invc_del_f1 invc_del_f2 invc_del_f3 invc_del_f4 invc_del_f5 invc_del_f6)

theorem invc_delete: "llrb t \<Longrightarrow> invc (delete x t)"
  by(simp add: delete_def invc_del llrb_def)

subsection \<open>proof of delete\<close>

theorem llrb_delete: "llrb t \<Longrightarrow> llrb (delete x t)"
  by(metis color_paint_Black delete_def invc_delete invh_delete llrb_def)

end