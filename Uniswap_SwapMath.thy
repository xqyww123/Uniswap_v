theory Uniswap_SwapMath
  imports Uniswap_SqrtPriceMath Uniswap_Tick_Math
begin


abbreviation XOR (infixr "XOR" 35) where \<open>A XOR B \<equiv> (A \<and> B \<or> \<not> A \<and> \<not> B)\<close>

definition swap_step :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real \<times> real \<times> real\<close>
  \<comment> \<open>As described in the white paper.
      Again we don't consider precision, so the specification can be simple and the difference
        between exactIn and exactOut disappears.
      The module of precision analysis will be designed after completing the \<phi>-system kernel
        and Solidity semantics.\<close>
  where \<open>swap_step price price_target L amount_remain \<gamma> = (
    let zeroForOne = (price >= price_target) ; \<comment> \<open>whether using token0 to buy token1\<close>
        exactIn = amount_remain \<ge> 0 ;
        amount_remain' = if exactIn then amount_remain * (1 - \<gamma>) else amount_remain ;
        max_amount = if zeroForOne XOR exactIn then L / price_target - L / price else L * (price_target - price) ;
        \<Delta>amount = if exactIn then min amount_remain' max_amount else max amount_remain' max_amount ;
        next_price = if L = 0 then price_target else if zeroForOne XOR exactIn then (L / (L / price + \<Delta>amount)) else price + \<Delta>amount / L ;
        amountIn = (if zeroForOne then L / next_price - L / price else L * (next_price - price)) ;
          \<comment> \<open>L / price is the reserve amount of token0, and L * price is that of token 1\<close>
        amountOut = (if zeroForOne then L * (price - next_price) else L / price - L / next_price) ;
        fee = amountIn * \<gamma> / (1 - \<gamma>)
     in (next_price, amountIn, amountOut, fee)
)\<close>

(* In swap_step, amount_remain cannot be zero *)

(* lemma
  \<open> 0 < price1 \<and> 0 < price_target \<and> 0 < price_target0 \<and> 0 \<le> L \<and> 0 < \<gamma> \<and> \<gamma> < 1
\<Longrightarrow> remain0 \<ge> 0
\<Longrightarrow> price_target0 \<le> price0 \<and> price_target \<le> price_target0
\<Longrightarrow> (price1, amt_in1, amt_out1, fee1) = swap_step price0 price_target0 L remain0 \<gamma>
\<Longrightarrow> (price2, amt_in2, amt_out2, fee2) = swap_step price1 price_target L (remain0 - (amt_in1 + fee1)) \<gamma>
\<Longrightarrow> (price3, amt_in3, amt_out3, fee3) = swap_step price0 price_target L remain0 \<gamma>
\<Longrightarrow> price3 = price2 \<and> amt_in1 + amt_in2 = amt_in3 \<and> amt_out1 + amt_out2 = amt_out3 \<and> fee1 + fee2 = fee3\<close>
  unfolding swap_step_def apply (auto simp add: min_def max_def)
     apply (cases \<open>L = 0\<close>)
      apply (simp add: Let_def)
apply (simp add: Let_def)
*)

declare [[linarith_split_limit = 30]]

lemma swap_step_fee_Le_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 \<le> fee\<close>
  unfolding swap_step_def Let_def
  apply auto
  apply (smt (verit, ccfv_SIG) divide_nonpos_pos frac_le mult.commute mult_less_0_iff pos_divide_le_eq times_divide_eq_left)
  apply (smt (verit, del_insts) divide_cancel_left divide_divide_eq_right divide_nonneg_pos divide_pos_pos eq_divide_imp frac_le less_eq_real_def mult_less_0_iff mult_nonneg_nonneg nonzero_mult_divide_mult_cancel_left2 nonzero_mult_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_right2 not_less_iff_gr_or_eq zero_less_mult_iff)
  by (simp add: frac_le)

lemma price_inequaty:
  \<open>0 < delta \<and> 0 < L \<and> 0 < price \<Longrightarrow> L / (L / price + delta) < price\<close> for L :: real
  by (smt (verit, del_insts) divide_cancel_right divide_pos_pos nonzero_mult_div_cancel_left pos_divide_le_eq)

lemma price_inequaty':
  \<open>0 \<le> delta \<and> 0 < L \<and> 0 < price \<Longrightarrow> L / (L / price + delta) \<le> price\<close> for L :: real
  by (smt (verit) divide_divide_eq_right nonzero_mult_div_cancel_left price_inequaty)

lemma price_inequaty2:
  \<open>0 < L / price + delta \<and> delta < 0 \<and> 0 < L \<and> 0 < price \<Longrightarrow> price < L / (L / price + delta)\<close> for L :: real
  by (smt (verit) mult.commute pos_divide_le_eq)

lemma price_inequaty2':
  \<open>0 < L / price + delta \<and> delta \<le> 0 \<and> 0 < L \<and> 0 < price \<Longrightarrow> price \<le> L / (L / price + delta)\<close> for L :: real
  by (smt (verit) ln_div ln_le_cancel_iff zero_less_divide_iff)
  

lemma swap_step_next_price_Le:
  \<open>0 < min_price \<and> min_price \<le> price \<and> min_price < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> min_price < next_price\<close>
  unfolding swap_step_def Let_def
  apply (cases \<open>price >= price_target\<close>; auto simp add: min_def max_def)
  apply (smt (verit, ccfv_SIG) divide_divide_eq_right mult_eq_0_iff nonzero_mult_div_cancel_left times_divide_eq_left zero_less_mult_iff)
  subgoal premises prems proof -
    have t1: \<open>0 < amount_remain * (1 - feePips)\<close>
      using prems(1) prems(11) prems(14) by fastforce
    thm prems
    have t2: \<open>L / price + amount_remain * (1 - feePips) \<le> L / price_target\<close>
      using prems(12) by force
    have t3: \<open>0 < L / price + amount_remain * (1 - feePips)\<close>
      by (smt (verit, best) divide_nonneg_nonneg prems(2) prems(3) prems(6) prems(9) t1)
    have t4: \<open>price_target \<le> L / (L / price + amount_remain * (1 - feePips))\<close>
      by (metis (no_types, opaque_lifting) divide_pos_pos linorder_linear linorder_not_less mult.commute order_antisym order_less_le_trans pos_le_divide_eq prems(15) prems(9) t2 t3)
    show ?thesis
      using prems(6) t4 by fastforce
  qed
  apply (smt (verit, ccfv_threshold) mult.commute pos_divide_le_eq)
  apply (smt (verit, best) frac_less2 split_mult_neg_le)
     apply (smt (verit) divide_pos_pos mult_pos_pos)
  apply (smt (verit, ccfv_threshold) price_inequaty2 zero_less_divide_iff)
  apply (smt (verit, ccfv_threshold) divide_pos_pos mult_pos_pos)
  by (smt (verit, del_insts) mult_less_0_iff)

lemma swap_step_next_price_Le_MIN_PRICE:
  \<open>MIN_PRICE \<le> price \<and> MIN_PRICE < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> MIN_PRICE < next_price\<close>
  using price_of_L0 swap_step_next_price_Le by blast

lemma swap_step_next_price_Gt:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price \<le> max_price \<and> price_target < max_price
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price < max_price\<close>
  unfolding swap_step_def Let_def
  apply (cases \<open>price >= price_target\<close>; auto simp add: min_def max_def)
  apply (smt (verit, del_insts) mult_nonneg_nonpos)
  apply (smt (verit, del_insts) mult_pos_pos price_inequaty)
  apply (smt (verit, best) divide_neg_pos)
  apply (smt (verit, del_insts) divide_neg_pos)
  apply (smt (verit, best) frac_le)
  apply (metis add.commute diff_less_eq divide_divide_eq_right frac_less2 leI nonzero_mult_div_cancel_left not_less_iff_gr_or_eq order_le_less_trans)
  apply (smt (verit, best) nonzero_mult_div_cancel_left pos_divide_le_eq)
  by (smt (verit, ccfv_SIG) mult_less_0_iff)

lemma swap_step_next_price_Gt_MAX:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price \<le> MAX_PRICE \<and> price_target < MAX_PRICE
\<Longrightarrow> amount_remain \<noteq> 0
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price < MAX_PRICE\<close>
  using swap_step_next_price_Gt .



lemma swap_step_next_price_Le_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 < next_price\<close>
  unfolding swap_step_def Let_def
  apply (auto)
  apply (smt (verit, best) divide_pos_pos mult_nonneg_nonneg)
  apply (smt (verit) mult_nonneg_nonneg zero_le_divide_iff)
  apply (smt (verit) divide_pos_pos)
  by (smt (verit, ccfv_SIG) nonzero_mult_div_cancel_left pos_divide_le_eq)

lemma swap_step_next_price_LE_price:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price_target \<le> price
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price \<le> price\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def)
     apply (smt (verit) divide_divide_eq_right nonzero_mult_div_cancel_left zero_le_mult_iff)
  subgoal premises prems proof -
    have x1: \<open>0 \<le> amount_remain * (1 - feePips)\<close>
      using prems(12) prems(9) by auto
    then show ?thesis
      by (smt (verit, del_insts) divide_eq_0_iff mult.commute pos_divide_le_eq prems(1) prems(3) prems(5))
  qed
  apply (smt (verit) minus_divide_left mult.commute mult_eq_0_iff mult_pos_pos pos_less_minus_divide_eq)
  by (simp add: divide_nonpos_pos)

lemma swap_step_price_target_LE_next_price:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price_target \<le> price
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> price_target \<le> next_price\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def)
  apply (smt (verit) divide_divide_eq_right nonzero_mult_div_cancel_left zero_le_mult_iff)
  subgoal premises prems proof -
    have t1: \<open>0 \<le> amount_remain * (1 - feePips)\<close>
      using prems(12) prems(9) by force
    then show ?thesis
      by (smt (verit, best) divide_pos_pos mult.commute pos_le_divide_eq prems(1) prems(10) prems(13) prems(3) prems(5))
  qed
  apply (smt (verit) mult.commute pos_divide_le_eq)
  by (smt (verit, best) frac_le mult_less_0_iff)

lemma swap_step_price_LE_next_price:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price < price_target
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> price \<le> next_price\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def not_le)
  subgoal premises prems proof -
    have t1: \<open>0 \<le> L / price + amount_remain\<close>
      by (smt (verit, best) divide_nonneg_pos prems(1) prems(10) prems(2) prems(5))
    then show ?thesis
      by (smt (verit, best) divide_le_0_iff mult.commute pos_le_divide_eq prems(1) prems(10) prems(11) prems(2))
  qed .

lemma swap_step_next_price_LE_price_target:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> price < price_target
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> next_price \<le> price_target\<close>
  unfolding swap_step_def Let_def
  apply (auto simp add: min_def max_def not_le)
  apply (smt (verit, best) frac_less2)
  apply (metis add.commute divide_divide_eq_right dual_order.order_iff_strict frac_less2 less_diff_eq linorder_not_le nonzero_mult_div_cancel_left order_le_less_trans)
  using divide_right_mono apply fastforce
  by (smt (verit, best) mult_less_0_iff)

lemma swap_step_amountIn_Le_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 \<le> amountIn\<close>
  unfolding swap_step_def Let_def
  apply auto
  using frac_le apply blast
  apply (smt (verit) divide_nonpos_pos frac_le mult.commute nonzero_mult_div_cancel_left pos_divide_le_eq)
  apply (auto simp add: min_def max_def not_le)
  by (smt (verit) divide_pos_pos eq_divide_imp frac_less2 mult_divide_mult_cancel_left_if nonzero_mult_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_right2 split_mult_pos_le times_divide_eq_left)

lemma swap_step_amountOut_0:
  \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L \<and> 0 < feePips \<and> feePips < 1
\<Longrightarrow> (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips
\<Longrightarrow> 0 \<le> amountOut\<close>
unfolding swap_step_def Let_def
  apply (clarsimp simp add: max_def min_def)
  apply (simp add: mult_nonneg_nonpos)
  apply (simp add: frac_le)
  apply (auto simp add: not_le)
  apply (smt (verit, del_insts) add_cancel_right_right divide_divide_eq_right mult_le_0_iff mult_not_zero nonzero_mult_div_cancel_left)
  apply (smt (verit, best) mult_le_cancel_left2)
  apply (smt (verit, best) mult_le_cancel_left2)
  subgoal premises prems
  proof -
    have t1: \<open>0 \<le> amount_remain * (1 - feePips)\<close>
      using prems(12) prems(8) by fastforce
    have t2: \<open>L / (L / price + amount_remain * (1 - feePips)) \<le> price\<close>
      by (smt (verit) divide_pos_pos mult.commute pos_divide_le_eq prems(13) prems(14) prems(2) prems(4) t1)
    show ?thesis
      by (simp add: prems(4) t2)
  qed .

proc computeSwapStep:
  input \<open>price \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> price_target \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> L \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amount_remain \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> feePips \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 < price \<and> 0 < price_target \<and> 0 \<le> L\<close>
      and  \<open>0 < feePips \<and> feePips < 1\<close>
  output \<open>next_price \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amountIn \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amountOut \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> fee \<Ztypecolon> \<v>\<a>\<l> \<real>
          \<s>\<u>\<b>\<j> next_price amountIn amountOut fee.
          (next_price, amountIn, amountOut, fee) = swap_step price price_target L amount_remain feePips\<close>
  is [routine]
  \<medium_left_bracket>
    var next_price, feeAmount ;;
    \<open>0 \<Ztypecolon> \<real>\<close> \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> var amountIn, amountOut (*TODO: support converge-of-branch between initialized and uninitialized variables*)
    \<open>$price \<ge> $price_target\<close> \<rightarrow> val zeroForOne ;;
    \<open>$amount_remain \<ge> 0\<close> \<rightarrow> val exactIn

    text \<open>We use some local definitions that save us from the very long expressions.\<close>

    define amount_remain' where \<open>amount_remain' = (if ?exactIn then amount_remain * (1 - feePips) else amount_remain)\<close>
    define max_amount where \<open>max_amount =
        (if ?zeroForOne XOR ?exactIn then L / price_target - L / price else L * (price_target - price))\<close>
    define \<Delta>amount where \<open>\<Delta>amount = (if ?exactIn then min amount_remain' max_amount else max amount_remain' max_amount)\<close>
    define next_price where \<open>next_price =
        (if L = 0 then price_target else if ?zeroForOne XOR ?exactIn then (L / (L / price + \<Delta>amount)) else price + \<Delta>amount / L)\<close> 
    define amountIn where \<open>amountIn =
        (if ?zeroForOne then L / next_price - L / price else L * (next_price - price))\<close>
    define amountOut where \<open>amountOut =
        (if ?zeroForOne then L * (price - next_price) else L / price - L / next_price)\<close> ;;

    if \<open>$exactIn\<close> \<medium_left_bracket>
      \<open>$amount_remain * (1 - $feePips)\<close> \<rightarrow> val amountRemainingLessFee ;;
      if \<open>$zeroForOne\<close> \<medium_left_bracket> getAmount0Delta ($price_target, $price, $L) \<medium_right_bracket>.
                       \<medium_left_bracket> getAmount1Delta ($price, $price_target, $L) \<medium_right_bracket>. \<rightarrow> amountIn ;;
      if \<open>$amountRemainingLessFee \<ge> $amountIn\<close> \<medium_left_bracket>
          $price_target \<rightarrow> next_price
      \<medium_right_bracket>. \<medium_left_bracket>
          getNextSqrtPriceFromInput ($price, $L, $amountRemainingLessFee, $zeroForOne)
          affirm using \<phi> by auto (smt (verit, best) divide_cancel_left mult_cancel_left2 zero_le_mult_iff) ;; \<rightarrow> next_price
      \<medium_right_bracket>. is \<open>next_price\<close> 
          affirm using \<phi> by (auto simp add: \<Delta>amount_def max_amount_def amount_remain'_def next_price_def)
    \<medium_right_bracket>. \<medium_left_bracket>
      if \<open>$zeroForOne\<close> \<medium_left_bracket> getAmount1Delta ($price_target, $price, $L) \<medium_right_bracket>.
                       \<medium_left_bracket> getAmount0Delta ($price, $price_target, $L) \<medium_right_bracket>. \<rightarrow> amountOut ;;
      if \<open>-$amount_remain \<ge> $amountOut\<close> \<medium_left_bracket>
          $price_target \<rightarrow> next_price
      \<medium_right_bracket>. \<medium_left_bracket>
          getNextSqrtPriceFromOutput ($price, $L, neg ($amount_remain), $zeroForOne) ;;
            affirm using \<phi> by (auto simp add: not_le) (smt (verit, best) divide_cancel_left left_diff_distrib) ;;
            affirm using \<phi> by (auto simp add: not_le)  (smt (verit, best) \<open>0 < price \<and> 0 < L\<close> mult.commute pos_less_minus_divide_eq)
          ;; \<rightarrow> next_price
      \<medium_right_bracket>. is \<open>next_price\<close>
          affirm using \<phi> apply (auto simp add: not_le \<Delta>amount_def max_amount_def amount_remain'_def next_price_def)
                          apply (smt (verit, best) mult_minus_right nonzero_mult_div_cancel_left)
                          apply (smt (verit, best) mult_minus_right)
                          apply (smt (verit, best) frac_le)
                          by (metis max.absorb3 minus_diff_eq minus_less_iff mult_minus_right)
    \<medium_right_bracket>. ;;

    \<open>$price_target = $next_price\<close> \<rightarrow> val max ;;

    text \<open>Now we claim two intermediate lemmas that will help the later construction.\<close>

    have t1[simp]: \<open>?zeroForOne \<Longrightarrow> price_target \<le> next_price \<and> next_price \<le> price\<close>
      unfolding \<Delta>amount_def max_amount_def amount_remain'_def next_price_def
      using \<phi> apply (auto simp add: min_def max_def not_le)
      apply (smt (verit) divide_pos_pos mult.commute mult_nonneg_nonneg pos_le_divide_eq)
      apply (metis diff_ge_0_iff_ge diff_self divide_divide_eq_right linorder_not_less mult_pos_neg mult_zero_left mult_zero_right nat_arith.rule0 nonzero_mult_div_cancel_left order_antisym order_trans)
      apply (smt (verit, del_insts) divide_pos_pos mult.commute pos_le_divide_eq split_mult_pos_le)
      apply (smt (verit, ccfv_threshold) divide_pos_pos mult.commute mult_nonneg_nonneg pos_divide_le_eq)
      apply (smt (verit, ccfv_SIG) mult.commute pos_le_divide_eq)
      apply (simp add: divide_nonpos_pos)
      apply (smt (verit, ccfv_SIG) divide_le_cancel nonzero_mult_div_cancel_left)
      by (simp add: divide_nonpos_pos)

    have t2[simp]: \<open>\<not> ?zeroForOne \<Longrightarrow> price \<le> next_price \<and> next_price \<le> price_target\<close>
      unfolding \<Delta>amount_def max_amount_def amount_remain'_def next_price_def
      using \<phi> apply (auto simp add: min_def max_def not_le)
      apply (smt (verit, ccfv_SIG) frac_less2)
      apply (smt (verit, del_insts) divide_divide_eq_right divide_pos_pos frac_le linorder_not_less nonzero_mult_div_cancel_left)
      apply (smt (verit, del_insts) divide_pos_pos mult.commute pos_divide_le_eq)
      using divide_right_mono apply fastforce
      apply (smt (verit, best) mult_less_0_iff)
      by (smt (verit, best) mult_less_0_iff) ;;

    if \<open>$zeroForOne\<close>
       \<medium_left_bracket>
      if \<open>$max \<and> $exactIn\<close> \<medium_left_bracket> $amountIn \<medium_right_bracket>. \<medium_left_bracket>
        getAmount0Delta ($next_price, $price, $L) affirm using \<phi> t1 by (auto; linarith) ;; \<medium_right_bracket>.
      \<rightarrow> amountIn is amountIn affirm unfolding amountIn_def using \<phi> by auto ;;
      if \<open>$max \<and> \<not> $exactIn\<close> \<medium_left_bracket> $amountOut \<medium_right_bracket>. \<medium_left_bracket>
        getAmount1Delta ($next_price, $price, $L) affirm using \<phi> t1 by (auto; linarith) ;; \<medium_right_bracket>.
      \<rightarrow> amountOut is amountOut affirm unfolding amountOut_def using \<phi> by auto
    \<medium_right_bracket>. \<medium_left_bracket>
      if \<open>$max \<and> $exactIn\<close> \<medium_left_bracket> $amountIn \<medium_right_bracket>. \<medium_left_bracket>
        getAmount1Delta ($price, $next_price, $L) \<medium_right_bracket>.
      \<rightarrow> amountIn is amountIn affirm unfolding amountIn_def using \<phi> by auto ;;
      if \<open>$max \<and> \<not> $exactIn\<close> \<medium_left_bracket> $amountOut \<medium_right_bracket>. \<medium_left_bracket>
        getAmount0Delta ($price, $next_price, $L) \<medium_right_bracket>.
      \<rightarrow> amountOut is amountOut affirm unfolding amountOut_def using \<phi> by auto
    \<medium_right_bracket>. ;;
  
  have t3: \<open>\<not> ?exactIn \<Longrightarrow> amountOut \<le> - amount_remain\<close>
    unfolding amountOut_def next_price_def \<Delta>amount_def amount_remain'_def max_amount_def
    using \<phi> by auto
  text \<open>Therefore, when there is no precision lost, the following branch will never be entered\<close> ;;

  if \<open>\<not> $exactIn \<and> $amountOut > - $amount_remain\<close> \<medium_left_bracket>
    \<open>- $amount_remain\<close> \<rightarrow> amountOut
  \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. is amountOut affirm using t3 by auto ;;

  if \<open>$exactIn \<and> $next_price \<noteq> $price_target\<close> \<medium_left_bracket>
    \<open>$amount_remain - $amountIn\<close> \<rightarrow> feeAmount is \<open>amountIn * feePips / (1 - feePips)\<close>
    affirm using \<phi> by (auto simp add: amountIn_def next_price_def \<Delta>amount_def amount_remain'_def max_amount_def min_def;
                       simp add: right_diff_distrib' right_diff_distrib)
  \<medium_right_bracket>. \<medium_left_bracket> \<open>$amountIn * $feePips / (1 - $feePips)\<close> \<rightarrow> feeAmount \<medium_right_bracket>. ;;

  return ($next_price, $amountIn, $amountOut, $feeAmount)
    affirm using \<phi> by (auto simp add: swap_step_def Let_def amountIn_def next_price_def \<Delta>amount_def
                                      amount_remain'_def max_amount_def amountOut_def)
  \<medium_right_bracket>. .

end