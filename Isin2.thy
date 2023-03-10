section \<open>Function \textit{isin} for Search_Tree2\<close>

theory Isin2
imports
  Search_Tree2
  Cmp
  Set_Specs
begin

fun isin :: "('a::linorder*'b) search_tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l (a,_) r) x =
  (case cmp x a of
     LT \<Rightarrow> isin l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin r x)"

lemma isin_set_inorder: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> set(inorder t))"
by (induction t rule: search_tree2_induct) (auto simp: isin_simps)

lemma isin_set_tree: "bst t \<Longrightarrow> isin t x \<longleftrightarrow> x \<in> set_search_tree t"
by(induction t rule: search_tree2_induct) auto

end