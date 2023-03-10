theory  Search_Tree2
imports Search_Tree
begin          

lemmas search_tree2_induct = search_tree.induct[where 'a = "'a * 'b", split_format(complete)]

lemmas search_tree2_cases = search_tree.exhaust[where 'a = "'a * 'b", split_format(complete)]

fun inorder :: "('a*'b)search_tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node l (a,_) r) = inorder l @ a # inorder r"

fun set_search_tree :: "('a*'b) search_tree \<Rightarrow> 'a set" where
"set_search_tree Leaf = {}" |
"set_search_tree (Node l (a,_) r) = {a} \<union> set_search_tree l \<union> set_search_tree r"

fun bst :: "('a::linorder*'b) search_tree \<Rightarrow> bool" where
"bst Leaf = True" |
"bst (Node l (a, _) r) = ((\<forall>x \<in> set_search_tree l. x < a) \<and> (\<forall>x \<in> set_search_tree r. a < x) \<and> bst l \<and> bst r)"

lemma finite_set_search_tree[simp]: "finite(set_search_tree t)"
by(induction t) auto

lemma eq_set_search_tree_empty[simp]: "set_search_tree t = {} \<longleftrightarrow> t = Leaf"
by (cases t) auto

lemma set_inorder[simp]: "set (inorder t) = set_search_tree t"
by (induction t) auto

lemma length_inorder[simp]: "length (inorder t) = size t"
by (induction t) auto

end