theory proof_insert
  imports
  LLRB_SET
begin

subsection \<open>functional implementation of llrb's insert operation\<close>

definition empty :: "'a llrb" where
"empty = Leaf"

fun color :: "'a llrb \<Rightarrow> color" where
"color Leaf = Black" |
"color (Node _ (_, c) _) = c"

fun bheight :: "'a llrb \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node l (x, c) r) = (if c = Black then bheight l + 1 else bheight l)"

fun invh :: "'a llrb \<Rightarrow> bool" where
"invh Leaf = True" |
"invh (Node l (x, c) r) = (bheight l = bheight r \<and> invh l \<and> invh r)"

fun invc :: "'a llrb \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node l (a,c) r) = ((c = Red \<longrightarrow> color l = Black \<and> color r = Black) \<and>
                         (c = Black \<longrightarrow> color r  = Red \<longrightarrow> color l = Red) \<and> invc l \<and> invc r)"

definition llrb :: "'a llrb \<Rightarrow> bool" where
"llrb t = (invc t \<and> invh t \<and> color t = Black)"

fun rightredB :: "'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"rightredB (B t1 a t2) b (R t3 c t4) = B (R (B t1 a t2) b t3) c t4"|
"rightredB Leaf a (R t1 b t2) = B (R Leaf a t1) b t2"|
"rightredB t1 a t2 = B t1 a t2"

fun baliL :: "'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"baliL (R t1 a (R t2 b t3)) c t4 = R (B t1 a t2) b (rightredB t3 c t4)" |
"baliL (R (R t1 a t2) b t3) c t4 = R (B t1 a t2) b (rightredB t3 c t4)" |
"baliL t1 a t2 = rightredB t1 a t2"

fun baliR :: "'a llrb \<Rightarrow> 'a \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"baliR t1 a (R t2 b (R t3 c t4)) = R (rightredB t1 a t2) b (B t3 c t4)" |
"baliR t1 a (R (R t2 b t3) c t4) = R (B t1 a t2) b (rightredB t3 c t4)" |
"baliR t1 a t2 = rightredB t1 a t2"

fun ins :: "'a::linorder \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"ins x Leaf = R Leaf x Leaf" |
"ins x (B l a r) =
  (case cmp x a of
     LT \<Rightarrow> baliL (ins x l) a r |
     GT \<Rightarrow> baliR l a (ins x r) |
     EQ \<Rightarrow> B l a r)" |
"ins x (R l a r) =
  (case cmp x a of
    LT \<Rightarrow> R (ins x l) a r |
    GT \<Rightarrow> R l a (ins x r) |
    EQ \<Rightarrow> R l a r)"

definition insert :: "'a::linorder \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
"insert x t =  paint Black(ins x t)"

subsection \<open>proof of bst_insert\<close>

lemma bst_paint: "inorder(paint c t) = inorder t"
  by(induct t) 
  auto

lemma bst_rightredB:
  "inorder (rightredB l a r) = inorder l @ a # inorder r"
  by(cases "(l, a, r)" rule: rightredB.cases) auto

lemma bst_baliR:
  "inorder(baliR l a r) = inorder l @ a # inorder r"
  by(cases "(l,a,r)" rule: baliR.cases)
  (auto simp: bst_rightredB)

lemma bst_baliL:
  "inorder(baliL l a r) = inorder l @ a # inorder r"
  by(cases "(l,a,r)"rule: baliL.cases)
  (auto simp: bst_rightredB)

lemma bst_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(ins x t) = ins_list x (inorder t)"
  by(induction x t rule: ins.induct)
  (auto simp: ins_list_simps bst_baliL bst_baliR)

theorem bst_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
  by(auto simp: insert_def bst_ins bst_paint)

subsection \<open>proof of invh_insert\<close>

lemma f1:
  "bheight t2 = 0 \<Longrightarrow> bheight (rightredB \<langle>\<rangle> a t2) = Suc 0"
  apply (induct t2)
  apply auto
  by (metis (full_types) rightredB.simps(2) Suc_eq_plus1 add_is_0 bheight.simps(1) bheight.simps(2) color.exhaust zero_neq_one)

lemma f2:
  "Suc (bheight v) = bheight t2 \<Longrightarrow> bheight (rightredB (B v vc vb) a t2) = Suc (bheight t2)"
  apply (induct t2)
  apply auto
  by (metis (full_types) Suc_eq_plus1 bheight.simps(2) color.exhaust rightredB.simps(1))

lemma bheight_rightredB: 
  "bheight l = bheight r \<Longrightarrow> bheight (rightredB l a r) = Suc (bheight l)"
  apply(induct l a r rule: baliL.induct)
  apply auto
  apply (simp add: f1)
  apply (simp add: f2)
  apply (smt (verit, del_insts) One_nat_def add_0 bheight.simps(1) bheight.simps(2) color.exhaust f2 rightredB.simps(5))
  apply (smt (verit) One_nat_def add.commute add_0 add_Suc_shift bheight.simps(2) color.exhaust f2 rightredB.simps(5))
  apply (simp add: f2)
  apply (metis (full_types) Suc_eq_plus1 bheight.simps(2) color.exhaust f2 rightredB.simps(5))
  apply (metis (full_types) Suc_eq_plus1 bheight.simps(2) color.exhaust f2 rightredB.simps(5))
  by (simp add: f2)

lemma bheight_baliL:
  "bheight l = bheight r \<Longrightarrow> bheight (baliL l a r) = Suc (bheight l)"
  by(induct l a r rule: baliL.induct)
  (auto simp: bheight_rightredB)
  
lemma bheight_baliR:
  "bheight l = bheight r \<Longrightarrow> bheight (baliR l a r) = Suc (bheight l)"
  by(induct l a r rule: baliR.induct) 
  (auto simp: bheight_rightredB)

lemma invh_rightredB:
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (rightredB l a r)"
  by(cases "(l,a,r)"rule: rightredB.cases)
  auto

lemma invh_baliL:
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliL l a r)"
  apply(induct l a r rule: baliL.induct) 
  by(auto simp: bheight_rightredB invh_rightredB)

lemma invh_baliR: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliR l a r)"
  by(induct l a r rule: baliR.induct)
  (auto simp: bheight_rightredB invh_rightredB)

lemma invh_bheight_rightredB:
  "\<lbrakk> invh l;  invh r;  bheight l  = bheight r \<rbrakk> \<Longrightarrow> invh (rightredB l a r) \<and> bheight (rightredB l a r) = Suc (bheight r)"
  apply (induct l a r rule: rightredB.induct)
  by simp+

lemma paint2: "paint c2 (paint c1 t) = paint c2 t"
  by(cases t) 
  auto

lemma invh_paint: "invh t \<Longrightarrow> invh (paint c t)"
  by(cases t)
  auto

lemma invh_ins: "invh t \<Longrightarrow> invh (ins x t) \<and> bheight (ins x t) = bheight t"
  by(induct x t rule: ins.induct)
  (auto simp: invh_baliL invh_baliR bheight_baliL bheight_baliR)

theorem invh_insert: "llrb t \<Longrightarrow> invh (insert x t)"
  by (auto simp: insert_def invh_ins invh_paint llrb_def)

subsection \<open>proof of invc_insert\<close>

lemma neq_Black[simp]: "(c \<noteq> Black) = (c = Red)"
  by(cases c) auto

lemma neq_Red[simp]: "(c \<noteq> Red) = (c = Black)"
  by(cases c) auto

abbreviation invc2 :: "'a llrb \<Rightarrow> bool" where
"invc2 t \<equiv> invc(paint Black t)"

lemma invc2I: "invc t \<Longrightarrow> invc2 t"
  apply(cases t rule: search_tree2_cases)
  apply simp+
  using neq_Black by blast

lemma color_rightredB:"color (rightredB l a r) = Black"
  apply (induct l a r rule: rightredB.induct)
  by auto

lemma invc_rightredB:"invc l \<Longrightarrow> invc r \<Longrightarrow> invc (rightredB l a r)"
  apply (induct l a r rule: rightredB.induct)
  by auto

fun invc3 :: "'a llrb \<Rightarrow> bool" where
"invc3 Leaf = True" |
"invc3 (Node l (a,c) r) = ((c = Red \<longrightarrow> color l = Black \<and> color r = Black) \<and> invc l \<and> invc r)"

fun ins_right_red :: "'a llrb \<Rightarrow> 'a llrb" where
"ins_right_red (Node l (a, Red) r) = (if(color l = Black \<and> color r = Red \<and> invc r \<and> invc3 l) then rightredB l a r else  (Node l (a, Black) r))" |
"ins_right_red Leaf = Leaf"|
"ins_right_red (B v vc vb) = (B v vc vb)"

abbreviation invc4 :: "'a llrb   \<Rightarrow> bool" where
"invc4 t  \<equiv> invc(ins_right_red t)"

fun invc_red :: "'a llrb \<Rightarrow> bool" where
"invc_red Leaf = True" |
"invc_red (Node l (a,c) r) = (invc4 (Node l (a,c) r) \<and> invc l \<and> invc r)"

lemma invc4I:"invc t \<Longrightarrow> invc4 t"
  apply(cases t rule: search_tree2_cases)
  apply simp
  by (metis (full_types) ins_right_red.simps(1) ins_right_red.simps(3) invc.simps(2) neq_Black)

lemma invc_redI:"invc t \<Longrightarrow> invc_red t"
  apply(cases t rule: search_tree2_cases)
  apply simp
  by (metis (full_types) ins_right_red.simps(1) ins_right_red.simps(3) invc.simps(2) invc_red.simps(2) neq_Black)

lemma invc_baliR1: "\<lbrakk>invc l; invc_red r\<rbrakk> \<Longrightarrow> invc_red (baliR l a r)"
  apply (induct l a r rule: baliR.induct)
  by (auto simp: invc_redI invc_rightredB)

lemma invc_baliR2: "\<lbrakk>invc l; invc_red r\<rbrakk> \<Longrightarrow> invc (baliR l a r)"
  apply (induct l a r rule: baliR.induct)
  apply auto
  by (auto simp: invc_rightredB color_rightredB)

lemma invc_baliR3: "\<lbrakk>invc_red l; invc r\<rbrakk> \<Longrightarrow> invc_red (baliL l a r)"
  apply (induct l a r rule: baliL.induct)
  by(auto simp:  invc_redI invc_rightredB)

lemma invc_baliR4: "\<lbrakk>invc_red l; invc r\<rbrakk> \<Longrightarrow> invc (baliL l a r)"
  apply (induct l a r rule: baliL.induct)
  by(auto simp:  invc_rightredB color_rightredB)

lemma color_paint_Black: "color (paint Black t) = Black"
  by(cases t) auto

lemma invc3I: "invc t \<Longrightarrow> invc3 t"
  apply(cases t rule: search_tree2_cases)
  by simp+

lemma invc_ins: "invc t \<longrightarrow> invc_red (ins x t) \<and> (color t = Black \<longrightarrow> invc (ins x t))"
  apply(induct x t rule: ins.induct)
  by(auto simp: invc_baliR1 invc_baliR2 invc3I invc_baliR3 invc_baliR4 invc_rightredB)

lemma invc2_ins:"invc t \<and> invh t \<and> color t = Black \<Longrightarrow> invc2 (ins x t)"
  by (simp add: invc2I invc_ins)

theorem invc_insert: "llrb t \<Longrightarrow> invc (insert x t)"
  by(simp add: llrb_def insert_def invc2_ins)  

subsection \<open>proof of insert\<close>

theorem llrb_insert: "llrb t \<Longrightarrow> llrb (insert x t)"
  by(metis invc_insert invh_insert llrb_def color_paint_Black insert_def)

end