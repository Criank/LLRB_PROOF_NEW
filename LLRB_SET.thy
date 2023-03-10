theory LLRB_SET
imports 
  Search_Tree2
  Cmp
  Set_Specs
  Sorted_Less
  List_Ins_Del
begin
datatype color = Red | Black
type_synonym 'a llrb = "('a*color) search_tree"

abbreviation R where "R l a r \<equiv> Node l (a, Red) r"
abbreviation B where "B l a r \<equiv> Node l (a, Black) r"

fun paint :: "color \<Rightarrow> 'a llrb \<Rightarrow> 'a llrb" where
   "paint c Leaf = Leaf" |
   "paint c (Node l (a,_) r) = Node l (a,c) r"
end
