theory Uniswap_SqrtPriceMath
  imports Uniswap_Common
begin

proc getAmount0Delta':
  \<comment> \<open>In this version we don't consider precision at all, so there is no rounding.
      Though it doesn't mean \<phi>-system currently has no ability to do precision analysis,
      I am thinking of a general framework in \<phi>-system boosting precision analysis,
      maybe based on relative error.\<close>
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 < rA \<and> 0 < rB \<and> 0 \<le> liq\<close>
  output \<open>\<bar>liq / rA - liq / rB\<bar> \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket> 
    $rA $rB \<rightarrow> var rA, rB ;;
    if \<open>$rA > $rB\<close> \<medium_left_bracket> $rB $rA \<rightarrow> rA, rB \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; 

    $liq \<rightarrow> val numerator1 ;;
    \<open>$rB - $rA\<close> \<rightarrow> val numerator2 ;;

    require (\<open> $rA > 0 \<close>) ;;

    \<open>$numerator1 * $numerator2 / $rA / $rB\<close>
  \<medium_right_bracket> using \<phi> apply auto
    apply (smt (verit, ccfv_SIG) diff_divide_distrib diff_frac_eq divide_strict_left_mono mult_pos_pos right_diff_distrib)
    by (smt (verit) diff_frac_eq divide_nonneg_nonneg right_diff_distrib' split_mult_pos_le) .

proc getAmount0Delta:
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 < rA \<and> rA \<le> rB\<close>
  output \<open>(liq / rA - liq / rB) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket> if \<open>$liq < 0\<close>
    \<medium_left_bracket> neg (getAmount0Delta'($rA, $rB, \<open>-$liq\<close>)) \<medium_right_bracket>.
    \<medium_left_bracket> getAmount0Delta'($rA, $rB, $liq) \<medium_right_bracket>.
  \<medium_right_bracket> using \<phi> apply auto
    apply (smt (z3) frac_le minus_divide_left)
    by (simp add: frac_le) .

proc getAmount1Delta':
  \<comment> \<open>In this version we don't consider precision at all, so there is no rounding.
      Though it doesn't mean \<phi>-system currently has no ability to do precision analysis,
      I am thinking of a general framework in \<phi>-system boosting precision analysis,
      maybe based on relative error.\<close>
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 < rA \<and> 0 < rB \<and> 0 \<le> liq\<close>
  output \<open>\<bar>liq * (rB - rA)\<bar> \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket> 
    $rA $rB \<rightarrow> var rA, rB ;;
    if \<open>$rA > $rB\<close> \<medium_left_bracket> $rB $rA \<rightarrow> rA, rB \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; 

    \<open>$liq * ($rB - $rA)\<close>
  \<medium_right_bracket> using \<phi> apply auto
    by (simp add: abs_mult) .

proc getAmount1Delta:
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 < rA \<and> rA \<le> rB\<close>
  output \<open>liq * (rB - rA) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket> if \<open>$liq < 0\<close>
    \<medium_left_bracket> neg (getAmount1Delta' ($rA, $rB, \<open>-$liq\<close>)) \<medium_right_bracket>.
    \<medium_left_bracket> getAmount1Delta' ($rA, $rB, $liq) \<medium_right_bracket>.
  \<medium_right_bracket> using \<phi> apply auto
    by (smt (verit, ccfv_threshold) zero_less_mult_iff) .



proc getAmount0Delta'_rounded:
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> roundUp \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < rA \<and> 0 < rB\<close>
  output \<open>(if roundUp then nat \<lceil> \<bar>real liq / rA - real liq / rB\<bar> \<rceil>
                      else nat \<lfloor> \<bar>real liq / rA - real liq / rB\<bar> \<rfloor>) \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  is [routine]
  \<medium_left_bracket>
    $rA $rB \<rightarrow> var rA, rB ;;
    if \<open>$rA > $rB\<close> \<medium_left_bracket> $rB $rA \<rightarrow> rA, rB \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; 

    $liq to_real \<rightarrow> val numerator1 ;;
    \<open>$rB - $rA\<close> \<rightarrow> val numerator2 ;;

    require (\<open> $rA > 0 \<close>) ;;

    if \<open>$roundUp\<close> \<medium_left_bracket>
      \<open>$numerator1 * $numerator2 / $rB / $rA\<close> (* is \<open>real liq * \<bar>rB - rA\<bar> / rB / rA\<close> *)
               (*The commented annotations are not required in the verification, but honestly
                 any programmer would like adding them during the development to make themselves
                 more clearly aware of the program. It is very natural for them who designed
                 the implementation to write down their original ideas.*)
        ceiling
    \<medium_right_bracket>. \<medium_left_bracket>
      \<open>$numerator1 * $numerator2 / $rB / $rA\<close> (* is \<open>real liq * \<bar>rB - rA\<bar> / rB / rA\<close> *) floor
    \<medium_right_bracket>.
  \<medium_right_bracket> using \<phi> apply auto
      apply (smt (verit, del_insts) divide_nonneg_pos mult_nonneg_nonneg mult_pos_pos of_nat_0_le_iff)
    apply (smt (verit, ccfv_SIG) diff_frac_eq divide_nonneg_nonneg mult.commute mult_nonneg_nonneg of_nat_0_le_iff right_diff_distrib)
    apply (smt (verit, best) diff_frac_eq divide_nonneg_pos mult.commute of_nat_0_le_iff right_diff_distrib' zero_less_mult_iff)
    apply (smt (verit, ccfv_threshold) divide_nonneg_nonneg mult_nonneg_nonneg of_nat_0_le_iff)
    apply (smt (verit, best) diff_frac_eq divide_nonneg_nonneg mult.commute mult_nonneg_nonneg of_nat_0_le_iff right_diff_distrib')
    by (smt (verit, ccfv_threshold) diff_frac_eq divide_nonneg_pos mult.commute of_nat_0_le_iff right_diff_distrib zero_less_mult_iff) .

proc getAmount0Delta_rounded:
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>0 < rA \<and> rA < rB\<close>
  output \<open>(if liq < 0 then \<lfloor> real_of_int liq / rB - real_of_int liq / rA \<rfloor>
                      else \<lceil> real_of_int liq / rA - real_of_int liq / rB \<rceil>) \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  is [routine]
  \<medium_left_bracket> if \<open>$liq < 0\<close>
    \<medium_left_bracket> $rA $rB \<open>-$liq\<close> \<open>False\<close> getAmount0Delta'_rounded \<medium_right_bracket>.
    \<medium_left_bracket> $rA $rB $liq \<open>True\<close> getAmount0Delta'_rounded \<medium_right_bracket>.
  \<medium_right_bracket> using \<phi> apply auto
    apply (smt (verit, ccfv_SIG) divide_minus_left frac_less2 of_int_less_0_iff)
    by (metis abs_of_nonneg diff_less_0_iff_less div_0 frac_less2 linorder_not_less not_less_iff_gr_or_eq of_int_0 of_int_pos) .



proc getNextSqrtPriceFromAmount0:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amount \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> add \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < liq \<and> 0 < sp\<close>
  output \<open> (if add then liq / (liq / sp + amount) else liq / (liq / sp - amount)) \<Ztypecolon> \<v>\<a>\<l> \<real> \<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$amount = 0\<close> \<medium_left_bracket> return ($sp) \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; (*Note, we have \<open>0 < amount\<close> in thm \<phi> now*)
    $liq \<rightarrow> val numerator1 ;;
    if \<open>$add\<close> \<medium_left_bracket>
      \<open>$amount * $sp\<close> \<rightarrow> val product ;;
      if \<open>$product / $amount = $sp\<close> \<medium_left_bracket>
        \<open>$numerator1 + $product\<close> \<rightarrow> val denominator ;;
        if \<open>$denominator \<ge> $numerator1\<close> \<medium_left_bracket>
          return (\<open>$numerator1 * $sp / $denominator\<close>)
            affirm using \<phi> by (simp add: add_frac_num) ;; (*TODO: add simplification before \<medium_right_bracket>. so this ;; can be removed*)
        \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
      \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;
      return ($numerator1 div (\<open>$numerator1 / $sp\<close> add ($amount)))
    \<medium_right_bracket>. \<medium_left_bracket>
      \<open>$amount * $sp\<close> \<rightarrow> val product ;;
      require (\<open>$product / $amount = $sp\<close>) ;;
      \<open>$numerator1 - $product\<close> \<rightarrow> val denominator ;;
      return (\<open>$numerator1 * $sp / $denominator\<close>)
      affirm using \<phi> by (simp add: add_divide_eq_if_simps(5))
    \<medium_right_bracket>. ;;
  \<medium_right_bracket>. .

proc getNextSqrtPriceFromAmount1:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amount \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> add \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>\<not> add \<longrightarrow> amount / liq < sp\<close>
  output \<open>(if add then sp + amount / liq else sp - amount / liq) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$add\<close> \<medium_left_bracket>
      \<open>$amount / $liq\<close> \<rightarrow> val quotient ;;
      return (\<open>$sp + $quotient\<close>)
    \<medium_right_bracket>. \<medium_left_bracket>
      \<open>$amount / $liq\<close> \<rightarrow> val quotient ;;
      require (\<open>$sp > $quotient\<close>) ;;
      return (\<open>$sp - $quotient\<close>)
    \<medium_right_bracket>. ;;
  \<medium_right_bracket>. .

proc getNextSqrtPriceFromInput:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amountIn \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < sp \<and> 0 < liq\<close>
  output \<open>(if zeroForOne then liq / (liq / sp + amountIn) else sp + amountIn / liq) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket>
    require (\<open>$sp > 0\<close>) ;;
    require (\<open>$liq > 0\<close>) ;;
    if \<open>$zeroForOne\<close> \<medium_left_bracket>
      getNextSqrtPriceFromAmount0 ($sp, $liq, $amountIn, \<open>True\<close>)
    \<medium_right_bracket>. \<medium_left_bracket>
      getNextSqrtPriceFromAmount1 ($sp, $liq, $amountIn, \<open>True\<close>)
    \<medium_right_bracket>. return (*it returns the result of the branch*)
  \<medium_right_bracket>. .

proc getNextSqrtPriceFromOutput:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> amountOut \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < sp \<and> 0 < liq\<close>
      and  \<open>zeroForOne \<longrightarrow> amountOut / liq < sp\<close>
  output \<open>(if zeroForOne then sp - amountOut / liq else liq / (liq / sp - amountOut)) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket>
    require (\<open>$sp > 0\<close>) ;;
    require (\<open>$liq > 0\<close>) ;;
    if \<open>$zeroForOne\<close> \<medium_left_bracket>
      getNextSqrtPriceFromAmount1 ($sp, $liq, $amountOut, \<open>False\<close>)
    \<medium_right_bracket>. \<medium_left_bracket>
      getNextSqrtPriceFromAmount0 ($sp, $liq, $amountOut, \<open>False\<close>)
    \<medium_right_bracket>. return (*it returns the result of the branch*)
  \<medium_right_bracket>. .




paragraph \<open>Liquidity formalization using integers\<close>

proc getNextSqrtPriceFromAmount0_int:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> amount \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> add \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < liq \<and> 0 < sp\<close>
  output \<open> (if add then liq / (liq / sp + amount) else liq / (liq / sp - amount)) \<Ztypecolon> \<v>\<a>\<l> \<real> \<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$amount = 0\<close> \<medium_left_bracket> return ($sp) \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; (*Note, we have \<open>0 < amount\<close> in thm \<phi> now*)
    $liq to_real \<rightarrow> val numerator1 ;;
    if \<open>$add\<close> \<medium_left_bracket>
      \<open>real $amount * $sp\<close> \<rightarrow> val product ;;
      if \<open>$product / real $amount = $sp\<close> \<medium_left_bracket>
        \<open>$numerator1 + $product\<close> \<rightarrow> val denominator ;;
        if \<open>$denominator \<ge> $numerator1\<close> \<medium_left_bracket>
          return (\<open>$numerator1 * $sp / $denominator\<close>)
            affirm using \<phi> by (simp add: add_frac_num) ;; (*TODO: add simplification before \<medium_right_bracket>. so this ;; can be removed*)
        \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>.
      \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;;
      return ($numerator1 div (\<open>$numerator1 / $sp\<close> add ($amount to_real)))
    \<medium_right_bracket>. \<medium_left_bracket>
      \<open>real $amount * $sp\<close> \<rightarrow> val product ;;
      require (\<open>$product / real $amount = $sp\<close>) ;;
      \<open>$numerator1 - $product\<close> \<rightarrow> val denominator ;;
      return (\<open>$numerator1 * $sp / $denominator\<close>)
      affirm using \<phi> by (simp add: add_divide_eq_if_simps(5))
    \<medium_right_bracket>. ;;
  \<medium_right_bracket>. .

proc getNextSqrtPriceFromAmount1_int:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> amount \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> add \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>\<not> add \<longrightarrow> real amount / real liq < sp\<close>
  output \<open>(if add then sp + amount / liq else sp - amount / liq) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$add\<close> \<medium_left_bracket>
      \<open>real $amount / real $liq\<close> \<rightarrow> val quotient ;;
      return (\<open>$sp + $quotient\<close>)
    \<medium_right_bracket>. \<medium_left_bracket>
      \<open>real $amount / real $liq\<close> \<rightarrow> val quotient ;;
      require (\<open>$sp > $quotient\<close>) ;;
      return (\<open>$sp - $quotient\<close>)
    \<medium_right_bracket>. ;;
  \<medium_right_bracket>. .

proc getNextSqrtPriceFromInput_int:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> amountIn \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < sp \<and> 0 < liq\<close>
  output \<open>(if zeroForOne then liq / (liq / sp + real amountIn) else sp + amountIn / liq) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket>
    require (\<open>$sp > 0\<close>) ;;
    require (\<open>$liq > 0\<close>) ;;
    if \<open>$zeroForOne\<close> \<medium_left_bracket>
      getNextSqrtPriceFromAmount0_int ($sp, $liq, $amountIn, \<open>True\<close>)
    \<medium_right_bracket>. \<medium_left_bracket>
      getNextSqrtPriceFromAmount1_int ($sp, $liq, $amountIn, \<open>True\<close>)
    \<medium_right_bracket>. return (*it returns the result of the branch*)
  \<medium_right_bracket>. .

proc getNextSqrtPriceFromOutput_int:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> amountOut \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < sp \<and> 0 < liq\<close>
      and  \<open>real amountOut / real liq < sp\<close>
  output \<open>(if zeroForOne then sp - amountOut / liq else liq / (liq / sp - real amountOut)) \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  is [routine]
  \<medium_left_bracket>
    require (\<open>$sp > 0\<close>) ;;
    require (\<open>$liq > 0\<close>) ;;
    if \<open>$zeroForOne\<close> \<medium_left_bracket>
      getNextSqrtPriceFromAmount1_int ($sp, $liq, $amountOut, \<open>False\<close>)
    \<medium_right_bracket>. \<medium_left_bracket>
      getNextSqrtPriceFromAmount0_int ($sp, $liq, $amountOut, \<open>False\<close>)
    \<medium_right_bracket>. return (*it returns the result of the branch*)
  \<medium_right_bracket>. .


end