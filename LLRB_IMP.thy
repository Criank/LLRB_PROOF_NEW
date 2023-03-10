theory LLRB_IMP
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

end