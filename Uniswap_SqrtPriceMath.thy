theory Uniswap_SqrtPriceMath
  imports UniSWP_Common
begin

proc getAmount0Delta':
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> roundUp \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < rA \<and> 0 < rB\<close>
  output \<open>(if roundUp then nat \<lceil> \<bar>real liq / rA - real liq / rB\<bar> \<rceil>
                      else nat \<lfloor> \<bar>real liq / rA - real liq / rB\<bar> \<rfloor>) \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  is [routine]
  \<medium_left_bracket>
    $rA $rB \<rightarrow> var rA, rB ;;
    if \<open>$rA > $rB\<close> \<medium_left_bracket> $rB $rA \<rightarrow> rA, rB \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; 

    $liq to_real \<rightarrow> val numerator1 ;;
    \<open>$rB - $rA\<close> (* is \<open>\<bar>rB - rA\<bar>\<close> *) \<rightarrow> val numerator2 ;;

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
    \<medium_right_bracket>. ;;
  \<medium_right_bracket> using \<phi> apply auto
      apply (smt (verit, del_insts) divide_nonneg_pos mult_nonneg_nonneg mult_pos_pos of_nat_0_le_iff)
    apply (smt (verit, ccfv_SIG) diff_frac_eq divide_nonneg_nonneg mult.commute mult_nonneg_nonneg of_nat_0_le_iff right_diff_distrib)
    apply (smt (verit, best) diff_frac_eq divide_nonneg_pos mult.commute of_nat_0_le_iff right_diff_distrib' zero_less_mult_iff)
    apply (smt (verit, ccfv_threshold) divide_nonneg_nonneg mult_nonneg_nonneg of_nat_0_le_iff)
    apply (smt (verit, best) diff_frac_eq divide_nonneg_nonneg mult.commute mult_nonneg_nonneg of_nat_0_le_iff right_diff_distrib')
    by (smt (verit, ccfv_threshold) diff_frac_eq divide_nonneg_pos mult.commute of_nat_0_le_iff right_diff_distrib zero_less_mult_iff) .

proc getAmount0Delta:
  input \<open>rA \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> rB \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  premises \<open>0 < rA \<and> rA < rB\<close>
  output \<open>(if liq < 0 then \<lfloor> real_of_int liq / rB - real_of_int liq / rA \<rfloor>
                      else \<lceil> real_of_int liq / rA - real_of_int liq / rB \<rceil>) \<Ztypecolon> \<v>\<a>\<l> \<int>\<close>
  is [routine]
  \<medium_left_bracket> if \<open>$liq < 0\<close>
    \<medium_left_bracket> $rA $rB \<open>-$liq\<close> \<open>False\<close> getAmount0Delta' \<medium_right_bracket>.
    \<medium_left_bracket> $rA $rB $liq \<open>True\<close> getAmount0Delta' \<medium_right_bracket>. ;;
  \<medium_right_bracket> using \<phi> apply auto
    apply (smt (verit, ccfv_SIG) divide_minus_left frac_less2 of_int_less_0_iff)
    by (metis abs_of_nonneg diff_less_0_iff_less div_0 frac_less2 linorder_not_less not_less_iff_gr_or_eq of_int_0 of_int_pos) .



proc getNextSqrtPriceFromAmount0RoundingUp:
  input \<open>sp \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> liq \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> amount \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> add \<Ztypecolon> \<v>\<a>\<l> \<bool>\<close>
  premises \<open>0 < liq\<close>
  output \<open> (if add then liq / (liq / sp + amount) else liq / (liq / sp - amount)) \<Ztypecolon> \<v>\<a>\<l> \<real> \<close>
  is [routine]
  \<medium_left_bracket>
    if \<open>$amount = 0\<close> \<medium_left_bracket> return ($sp) \<medium_right_bracket>. \<medium_left_bracket> \<medium_right_bracket>. ;; (*Note, we have \<open>0 < amount\<close> in thm \<phi> now*)
    $liq to_real \<rightarrow> val numerator1 ;;

if \<open>$add\<close> \<medium_left_bracket>
  ;; \<open>real ($amount)\<close>
  ;; \<open>real_of_int ($amount)\<close>
  ;;
      \<open>$amount * $sp\<close> 




end