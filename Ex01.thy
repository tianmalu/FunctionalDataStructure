theory Ex01
imports Main
begin

value "2 + (2::nat)"
value "(2::nat)*(5+3)"
value "(3::nat)*4-2*(7+1)"

lemma "(a::nat) +b = b + a"
  apply(auto)
  done

lemma "(a::nat)+ b + c = a+ (b+c)" by auto

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"
value "count [1,2,2,7,2,2,2,4](2::nat)"

theorem "count xs x \<le> length xs" 
  apply (induct xs)
   apply auto
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (y#ys) x = y#(snoc ys x)"
value "snoc [] c"

lemma "snoc [] c =[c]" by auto

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x#xs) = snoc (reverse xs) x"


value "reverse [a, b, c]"
lemma "reverse [a, b, c] = [c, b, a]" by auto


lemma reverse_snoc[simp]: "reverse (snoc xs x) = x#reverse xs"
 apply (induction xs)
 apply auto
  done

lemma"reverse(reverse []) = []" by auto
theorem "reverse(reverse xs) = xs" 
  apply (induction xs)
   apply simp
  apply simp
  done
end

