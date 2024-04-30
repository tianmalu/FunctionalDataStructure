theory Submission
  imports Defs
begin

fun oddsum :: "nat \<Rightarrow> nat"  where
  "oddsum 0 = 0" |
  "oddsum x = oddsum (x-1) + 2*x-1"

value "oddsum 3 = 5 + 3 + 1 + 0"
value "oddsum 7 = 49"
value "oddsum 1 = 1"

lemma oddsum_is_square: "oddsum n = n * n" 
  apply (induction n)
   apply simp
  apply simp
  done

lemma oddsum_mult: "oddsum (n*m) = oddsum n * oddsum m"
  by(auto simp add: oddsum_is_square)

fun spread :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
  "spread x [] = []"|
  "spread x (y#ys) = y # x # (spread x ys)"

value "spread (0::nat) [1,2,3]"
value "spread (0::nat) [1,2,3] = [1,0,2,0,3,0]"

lemma count_spread: "count (spread a xs) a = count xs a + length xs"
  apply (induction xs)
   apply simp
  apply simp
  done

value "snoc (reverse (spread (0::nat) [1,2,3])) 0"

lemma spread_snoc:
  "snoc (snoc (spread a xs) b) a = spread a (snoc xs b)"
  apply (induction xs)
   apply simp
  apply simp
  done


lemma spread_reverse_snoc: "snoc (reverse (spread a xs)) a = a # spread a (reverse xs)"
  apply (induction xs)
   apply auto
  apply (simp add:spread_snoc)
  done

end


