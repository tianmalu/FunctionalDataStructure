theory Submission
  imports Defs
begin

fun collect :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b list"  where
  "collect _ [] = []"|
"collect a ((x,v)#xs) = (if a=x then v#collect a xs else collect a xs)"

definition ctest :: "(int * int) list" where "ctest \<equiv> [
    (2,3),(2,5),(2,7),(2,9), 
    (3,2),(3,4),(3,5),(3,7),(3,8),
    (4,3),(4,5),(4,7),(4,9),
    (5,2),(5,3),(5,4),(5,6),(5,7),(5,8),(5,9),
    (6,5),(6,7),
    (7,2),(7,3),(7,4),(7,5),(7,6),(7,8),(7,9),
    (8,3),(8,5),(8,7),(8,9),
    (9,2),(9,4),(9,5),(9,7),(9,8)
  ]"

value "collect 3 ctest = [2,4,5,7,8]"
value "collect 1 ctest = []"


lemma collect_alt: "collect x ys = map snd (filter (\<lambda>kv. fst kv = x) ys)"
  apply (induction ys arbitrary:x)
   apply(simp)
  apply (auto)
  done

fun collect_tr :: "'a list \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'a) list \<Rightarrow> 'a list"  where
  "collect_tr acc _ [] = rev acc"
| "collect_tr acc x ((y, v)#ys) = (if x = y then collect_tr (v#acc) x ys else collect_tr acc x ys)"



lemma collect_tr_collect_general: "collect_tr acc x ys = rev acc @ collect x ys"
  apply(induction ys arbitrary: x acc)
   apply(simp)
  apply(auto)
  done

lemma collect_tr_collect: "collect_tr [] x ys = collect x ys"
    apply(simp add: collect_tr_collect_general)
    done

fun lheight :: "'a ltree \<Rightarrow> nat"  where
  "lheight (Leaf _) = 0"|
  "lheight (Node l r) = max(lheight l) (lheight r) +1"

fun num_leafs :: "'a ltree \<Rightarrow> nat"  where
  "num_leafs (Leaf _) = 1" |
  "num_leafs (Node l r) = num_leafs l + num_leafs r"

fun perfect :: "'a ltree \<Rightarrow> bool"  where
  "perfect (Leaf _) = True"|
  "perfect (Node l r) = (perfect l \<and> perfect r \<and> lheight l = lheight r)"

lemma perfect_num_leafs_height: "perfect t \<Longrightarrow> num_leafs t = 2^lheight t"
  apply(induction t )
   apply(simp)
  apply(auto)
  done
  
lemma set_shuffles: "zs \<in> set (shuffles xs ys) \<Longrightarrow> set zs = set xs \<union> set ys"
  apply(induction xs ys arbitrary: zs rule:shuffles.induct)
   apply(simp)
  apply(auto)
  done

end