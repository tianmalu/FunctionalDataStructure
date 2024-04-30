theory Ex02
  imports Main
begin

thm fold.simps

fun list_sum :: "nat list \<Rightarrow> nat"  where
  "list_sum [] = 0"|
  "list_sum (x#xs) = x+ list_sum(xs)"

definition list_sum' :: "nat list \<Rightarrow> nat"  where
  "list_sum' xs = fold (+) xs 0"

lemma a: "fold (+) xs a =  a+list_sum' xs"
  apply(induction xs arbitrary:a)
   apply auto
  sledgehammer
  sorry

lemma "list_sum xs = list_sum' xs"
  apply (induction xs)
   apply (simp add:list_sum'_def)
  done
  


datatype  'a ltree = Leaf 'a | Node "'a ltree" "'a ltree"

fun inorder :: "'a ltree \<Rightarrow> 'a list"  where
  "inorder (Leaf a) = [a]"|
  "inorder (Node l r) = inorder l @ inorder r"

fun fold_ltree :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a ltree \<Rightarrow> 'b \<Rightarrow> 'b" where
"fold_ltree f (Leaf a) s = f a s" |
"fold_ltree f (Node l r) s = fold_ltree f r (fold_ltree f l s)"

lemma "fold f (inorder t) s = fold_ltree f t s"
  apply (induction t arbitrary: s)
   apply(auto)
  done

fun mirror :: "'a ltree \<Rightarrow> 'a ltree" where
"mirror (Leaf a) = Leaf a" |
"mirror (Node l r) = Node (mirror r) (mirror l)"

lemma "inorder (mirror t) = rev (inorder t)"
  apply (induction t)
   apply (simp)
  apply (auto)

fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"shuffles [] ys = [ys]" |
"shuffles xs [] = [xs]" |
"shuffles (x#xs) (y#ys) = 
  map (\<lambda>zs. x # zs) (shuffles xs (y#ys)) @ 
  map (\<lambda>zs. y # zs) (shuffles (x#xs) ys)"

lemma "zs \<in> set (shuffles xs ys) \<Longrightarrow> length zs = length xs + length ys"
  sorry

end