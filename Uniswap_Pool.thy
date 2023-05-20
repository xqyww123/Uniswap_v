theory Uniswap_Pool
  imports Uniswap_SwapMath Uniswap_Tick_Math Uniswap_TickBitmap Uniswap_Tick
begin

type_synonym fee_protocol = \<open>nat \<times> nat\<close>

datatype pool = pool (price: real) (tick: int) (unlocked: bool) (liquidity: real)
                     (growth: growth) (fee_protocol: fee_protocol) (protocol_fees: \<open>fee \<times> fee\<close>)

hide_const (open) price tick unlocked liquidity growth fee_protocol protocol_fees

setup \<open>Sign.mandatory_path "pool"\<close>

definition \<open>map_price f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool (f p) t u l gr fp pf)\<close>
lemma map_price[simp]:
  \<open>pool.map_price f (pool p t u l gr fp pf) = pool (f p) t u l gr fp pf\<close>
  unfolding pool.map_price_def by simp

definition \<open>map_tick f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p (f t) u l gr fp pf)\<close>
lemma map_tick[simp]:
  \<open>pool.map_tick f (pool p t u l gr fp pf) = pool p (f t) u l gr fp pf\<close>
  unfolding pool.map_tick_def by simp

definition \<open>map_unlock f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t (f u) l gr fp pf)\<close>
lemma map_unlock[simp]:
  \<open>pool.map_unlock f (pool p t u l gr fp pf) = pool p t (f u) l gr fp pf\<close>
  unfolding pool.map_unlock_def by simp

definition \<open>map_liquidity f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u (f l) gr fp pf)\<close>
lemma map_liquidity[simp]:
  \<open>pool.map_liquidity f (pool p t u l gr fp pf) = pool p t u (f l) gr fp pf\<close>
  unfolding pool.map_liquidity_def by simp

definition \<open>map_growth f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u l (f gr) fp pf)\<close>
lemma map_growth[simp]:
  \<open>pool.map_growth f (pool p t u l gr fp pf) = pool p t u l (f gr) fp pf\<close>
  unfolding pool.map_growth_def by simp

definition \<open>map_fee_protocol f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u l gr (f fp) pf)\<close>
lemma map_fee_protocol[simp]:
  \<open>pool.map_fee_protocol f (pool p t u l gr fp pf) = pool p t u l gr (f fp) pf\<close>
  unfolding pool.map_fee_protocol_def by simp

definition \<open>map_protocal_fees f x = (case x of pool p t u l gr fp pf \<Rightarrow> pool p t u l gr fp (f pf))\<close>
lemma map_protocal_fees[simp]:
  \<open>pool.map_protocal_fees f (pool p t u l gr fp pf) = pool p t u l gr fp (f pf)\<close>
  unfolding pool.map_protocal_fees_def by simp

setup \<open>Sign.parent_path\<close>

  

lemma [\<phi>reason 1000]: \<open> Is_Literal fee\<close> unfolding Is_Literal_def ..

proc (nodef) fee[\<phi>synthesis 1100]:
  input \<open>Void\<close>
  output \<open>fee_rate \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  \<medium_left_bracket> apply_rule op_const_areal[where x=fee_rate] \<medium_right_bracket>.


locale Pool = Tickmap_spec + Tick_spec +
  fixes Pool :: \<open>(fiction, pool) \<phi>\<close>
    and op_get_pool_price :: \<open>VAL proc\<close>
    and op_set_pool_price :: \<open>(VAL,unit) proc'\<close>
    and op_get_pool_tick :: \<open>VAL proc\<close>
    and op_set_pool_tick :: \<open>(VAL,unit) proc'\<close>
    and op_get_pool_unlock :: \<open>VAL proc\<close>
    and op_set_pool_unlock :: \<open>(VAL,unit) proc'\<close>
    and op_get_liquidity :: \<open>VAL proc\<close>
    and op_set_liquidity :: \<open>(VAL,unit) proc'\<close>
    and op_get_fee_growth_0 :: \<open>VAL proc\<close>
    and op_set_fee_growth_0 :: \<open>(VAL,unit) proc'\<close>
    and op_get_fee_growth_1 :: \<open>VAL proc\<close>
    and op_set_fee_growth_1 :: \<open>(VAL,unit) proc'\<close>
    and op_get_fee_protocol_0 :: \<open>VAL proc\<close>
    and op_get_fee_protocol_1 :: \<open>VAL proc\<close>
    and op_get_protocal_fee_0 :: \<open>VAL proc\<close>
    and op_set_protocal_fee_0 :: \<open>(VAL,unit) proc'\<close>
    and op_get_protocal_fee_1 :: \<open>VAL proc\<close>
    and op_set_protocal_fee_1 :: \<open>(VAL,unit) proc'\<close>
  assumes [\<phi>inhabitance_rule]:
    \<open>s \<Ztypecolon> Pool \<i>\<m>\<p>\<l>\<i>\<e>\<s> UNIV \<a>\<n>\<d> 0 < pool.price s \<and> pool.tick s \<in> {MIN_TICK..<MAX_TICK}
                           \<and> pool.price s \<in> {MIN_PRICE..<MAX_PRICE}\<close>
  and get_pool_price_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_pool_price \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.price s \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_price_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_pool_price rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> p' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_price (\<lambda>_. p') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_tick_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_pool_tick \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.tick s \<Ztypecolon> \<v>\<a>\<l> Tick \<rbrace> \<close>
  and set_pool_tick_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_pool_tick ri \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> t' \<Ztypecolon> \<v>\<a>\<l>[ri] Tick \<longmapsto> pool.map_tick (\<lambda>_. t') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_unlock_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_get_pool_unlock \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.unlocked s \<Ztypecolon> \<v>\<a>\<l> \<bool> \<rbrace> \<close>
  and set_pool_unlock_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_pool_unlock rb \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> b' \<Ztypecolon> \<v>\<a>\<l>[rb] \<bool> \<longmapsto> pool.map_unlock (\<lambda>_. b') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_liquidity_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_liquidity \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> pool.liquidity s \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_liquidity_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_liquidity rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> l' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_liquidity (\<lambda>_. l') s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_fee_growth_0_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_growth_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> growth.fee0 (pool.growth s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_fee_growth_0_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_fee_growth_0 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_growth (growth.map_fee0 (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_fee_growth_1_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_growth_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> growth.fee1 (pool.growth s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_fee_growth_1_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_fee_growth_1 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_growth (growth.map_fee1 (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_fee_protocol_0_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_protocol_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> fst (pool.fee_protocol s) \<Ztypecolon> \<v>\<a>\<l> \<nat> \<rbrace> \<close>
  and get_fee_protocol_1_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_fee_protocol_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> snd (pool.fee_protocol s) \<Ztypecolon> \<v>\<a>\<l> \<nat> \<rbrace> \<close>
  and get_pool_protocal_fee_0_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_protocal_fee_0 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> fst (pool.protocol_fees s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_protocal_fee_0_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_protocal_fee_0 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_protocal_fees (apfst (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>
  and get_pool_protocal_fee_1_\<phi>app[\<phi>synthesis 1000]:
    \<open> \<p>\<r>\<o>\<c> op_get_protocal_fee_1 \<lbrace> s \<Ztypecolon> Pool \<longmapsto> s \<Ztypecolon> Pool\<heavy_comma> snd (pool.protocol_fees s) \<Ztypecolon> \<v>\<a>\<l> \<real> \<rbrace> \<close>
  and set_pool_protocal_fee_1_\<phi>app:
    \<open> \<p>\<r>\<o>\<c> op_set_protocal_fee_1 rv \<lbrace> s \<Ztypecolon> Pool\<heavy_comma> c' \<Ztypecolon> \<v>\<a>\<l>[rv] \<real> \<longmapsto> pool.map_protocal_fees (apsnd (\<lambda>_. c')) s \<Ztypecolon> Pool \<rbrace> \<close>

begin


definition Uniswap_Pool :: \<open>(fiction, price \<times> tick \<times> bool \<times> liquiditys \<times> liquiditys \<times> growths \<times> opt_growths \<times> fee_protocol \<times> (fee \<times> fee)) \<phi>\<close>
  where [\<phi>defs]: \<open>Uniswap_Pool x = (
    case x of (price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Rightarrow>
        \<comment> \<open>\<open>growth\<close> is the abstract growth happened on every tick\<close>
      pool price i unlocked (L i) (gSum growth) fee_proto protocol_fees \<Ztypecolon> Pool\<heavy_comma>
        \<comment> \<open>so the global fee growth is the sum of the \<open>growth\<close> over every tick\<close>
      (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
        \<comment> \<open>\<open>k \<in> dom \<delta>\<close> means the tick \<open>k\<close> is initialized\<close>
      (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks
    \<s>\<u>\<b>\<j> (tick_of_price price = i \<or> price = price_of (i + 1))
)\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 1200]:
  \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Ztypecolon> Uniswap_Pool \<i>\<m>\<p>\<l>\<i>\<e>\<s>
   pool price i unlocked (L i) (gSum growth) fee_proto protocol_fees \<Ztypecolon> Pool\<heavy_comma>
   (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
   (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks
  \<a>\<n>\<d> (tick_of_price price = i \<or> price = price_of (i + 1))
  @action to RAW\<close>
  \<medium_left_bracket> destruct\<phi> _ \<medium_right_bracket>.

lemma [\<phi>reason 100]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (tick_of_price price = i \<or> price = price_of (i + 1))
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> pool price i unlocked (L i) (gSum growth) fee_proto protocol_fees \<Ztypecolon> Pool\<heavy_comma>
        (\<lambda>k. 0 < Lg k) \<Ztypecolon> Tickmap\<heavy_comma>
        (Lg, L, growth, i, \<delta>) \<Ztypecolon> Ticks \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Ztypecolon> Uniswap_Pool \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> P\<close>
  unfolding FOCUS_TAG_def
  \<medium_left_bracket> premises _ and I
    I 
    construct\<phi> \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_proto, protocol_fees) \<Ztypecolon> Uniswap_Pool\<close>
  \<medium_right_bracket>.

declare Invt_Ticks_def[simp] Invt_A_Tick_def[simp]

definition \<open>\<Delta>protocal_fees fee_proto zeroForOne L price price' \<gamma>
    = (if zeroForOne
       then if 0 < fst fee_proto
            then (fst (reserve_change zeroForOne L price price') * fee_rate' / real (fst fee_proto), 0)
            else (0,0)
       else if 0 < snd fee_proto
            then (0, snd (reserve_change zeroForOne L price price') * fee_rate' / real (snd fee_proto))
            else (0,0))\<close>

proc swap:
  input \<open>(price, i, unlocked, Lg, L, growth, \<delta>, fee_protocol, protocol_fees) \<Ztypecolon> Uniswap_Pool\<heavy_comma>
         zeroForOne \<Ztypecolon> \<v>\<a>\<l> \<bool>\<heavy_comma> amount_specified \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> price_limit \<Ztypecolon> \<v>\<a>\<l> \<real>\<close>
  premises \<open>0 \<noteq> amount_specified \<and> 0 < price_limit\<close> and \<open>unlocked\<close>
      and \<open>if zeroForOne then price_limit < price \<and> price_limit > MIN_PRICE
                         else price_limit > price \<and> price_limit < MAX_PRICE\<close>
    (*soon we will not need to declare these pre-conditions but verify that
        a revert will happen once they are violated*)
  output \<open>(price', i', unlocked, Lg, L,
            growth + fee_growth zeroForOne fee_rate' L price price',
            \<delta>, fee_protocol,
            protocol_fees + \<Delta>protocal_fees fee_protocol zeroForOne L price price' fee_rate') \<Ztypecolon> Uniswap_Pool\<heavy_comma>
          transfer_out \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> transfer_in \<Ztypecolon> \<v>\<a>\<l> \<real>
    \<s>\<u>\<b>\<j> price' i' transfer_out transfer_in.
      (if zeroForOne then price_limit \<le> price' else price' \<le> price_limit) \<and>
      (price' = price_limit \<or> (
      if 0 < amount_specified
      then amount_specified * (1 - fee_rate) = (if zeroForOne then fst else snd) (reserve_change zeroForOne L price price')
      else - amount_specified = (if zeroForOne then snd else fst) (reserve_change zeroForOne L price price') ))
      \<comment> \<open>The resulted price either reaches the price limit, or, is the one having a reserve change
             meeting the specified amount.
          \<open>reserve_change zeroForOne L price price'\<close> is the reserve change of token0 and token1
             when the price is moving from \<open>price\<close> to \<open>price'\<close>\<close>
      \<comment> \<open>The tick \<open>i'\<close> is the one satisfying the global invariant encoded in \<^const>\<open>Uniswap_Pool\<close>,
          which is, \<open>i'\<close> is the tick of the \<open>price'\<close>, \<open>price_of i' \<le> price \<le> price_of (i' + 1)\<close>\<close>
      \<comment> \<open>Gross liquidity \<open>Lg\<close>, actual liquidity \<open>L\<close>, the absolute difference \<open>\<delta>\<close> in recorded fee growth,
          and the proportion \<open>fee_protocol\<close> of the protocol fee, are not changed\<close>
      \<comment> \<open>The fee growth \<open>growth + fee_growth zeroForOne fee_rate' L price price'\<close>
          and the \<open>protocol_fees\<close> are increased accordingly.\<close>
   \<and> transfer_out = (if zeroForOne then snd else fst) (reserve_change zeroForOne L price price')
   \<and> transfer_in = (if zeroForOne then fst else snd) (reserve_change zeroForOne L price price') / (1 - fee_rate)
    \<comment> \<open>As \<phi>-system hasn't formalized transfer and external call, we cannot verify the last transfer operation
      in the swap function, but only verify the amount of transfer-out and that of transfer-in. \<close>
\<close>
  is [routine]
  (* is [noDelegateCall]  Currently no modifier is supported, but is planned *)
  \<medium_left_bracket> D ;;
    require (\<open>$amount_specified \<noteq> 0\<close>) ;;
    require (get_pool_unlock) ;;
    require (
      sel ( \<open>$price_limit < (pool.price _) \<and> $price_limit > MIN_PRICE\<close>,
            \<open>$price_limit > (pool.price _) \<and> $price_limit < MAX_PRICE\<close>,
            $zeroForOne)) ;;
    set_pool_unlock (\<open>False\<close>)  ;;

    define fee_proto where \<open>fee_proto = (if zeroForOne then fst fee_protocol else snd fee_protocol)\<close> ;;
 
    get_pool_liquidity \<rightarrow> val liquidityStart
    sel (get_fee_protocol_0, get_fee_protocol_1, $zeroForOne)
        is fee_proto \<rightarrow> val feeProtocol
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> val secondsPerLiquidityCumulative
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> val tickCumulative

    (* no blockTimestamp because we don't cover observation *)

    \<open>$amount_specified > 0\<close> \<rightarrow> val exactInput

    define I_fee_growth_global where
      \<open>\<And>gr. I_fee_growth_global gr = (if zeroForOne then global_fee0_growth gr else global_fee1_growth gr)\<close> ;;

    $amount_specified \<rightarrow> var amount_remaining
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> var amount_calculated
    get_pool_price \<rightarrow> var price
    get_pool_tick \<rightarrow> var tick
    sel (\<open>growth.fee0 (pool.growth _)\<close> \<open>growth.fee1 (pool.growth _)\<close> $zeroForOne)
      is \<open>I_fee_growth_global growth\<close> \<rightarrow> var fee_growth_global
    \<open>0 \<Ztypecolon> \<real>\<close> \<rightarrow> var protocolFee
    $liquidityStart \<rightarrow> var liquidity ;;

    while \<open>ar \<Ztypecolon> \<v>\<a>\<r>[amount_remaining] \<real>\<heavy_comma>
           pr \<Ztypecolon> \<v>\<a>\<r>[price] \<real>\<heavy_comma>
           ac \<Ztypecolon> \<v>\<a>\<r>[amount_calculated] \<real>\<heavy_comma>
           pf \<Ztypecolon> \<v>\<a>\<r>[protocolFee] \<real>\<heavy_comma>
            j \<Ztypecolon> \<v>\<a>\<r>[tick] Tick\<heavy_comma>
           L j \<Ztypecolon> \<v>\<a>\<r>[liquidity] \<real>\<heavy_comma>
          I_fee_growth_global (growth + fee_growth zeroForOne fee_rate' L price pr) \<Ztypecolon> \<v>\<a>\<r>[fee_growth_global] \<real>\<heavy_comma>
          (Lg, L, growth + fee_growth zeroForOne fee_rate' L price pr, j, \<delta>) \<Ztypecolon> Ticks

        \<s>\<u>\<b>\<j> ar pr ac pf j.
          Inv: ( MIN_PRICE \<le> pr \<and> pr < MAX_PRICE
               \<and> j < MAX_TICK
               \<and> (tick_of_price pr = j \<or> pr = price_of (j + 1))
               \<and> (if zeroForOne then price_limit \<le> pr \<and> pr \<le> price else price \<le> pr \<and> pr \<le> price_limit)
               \<and> (let (\<Delta>reserve0, \<Delta>reserve1) = reserve_change zeroForOne L price pr;
                      amountIn = (if zeroForOne then \<Delta>reserve0 else \<Delta>reserve1) ;
                      amountOut = (if zeroForOne then \<Delta>reserve1 else \<Delta>reserve0)
                   in (if $exactInput then amount_specified - amountIn / (1 - fee_rate) else amount_specified + amountOut) = ar
                    \<and> (if $exactInput then - amountOut else amountIn / (1 - fee_rate)) = ac
                    \<and> (if 0 < fee_proto then amountIn * fee_rate' / real fee_proto else 0) = pf
               ))
          \<and> Guard: (ar \<noteq> 0 \<and> pr \<noteq> price_limit)\<close>
    \<medium_left_bracket> \<open>$amount_remaining \<noteq> 0 \<and> $price \<noteq> $price_limit\<close> \<medium_right_bracket>
    \<medium_left_bracket>
      $price \<rightarrow> val step_price_start ;;
      nextInitializedTickWithinOneWord ($tick, $zeroForOne) \<exists>tick_next' \<rightarrow> var tick_next, val initialized ;;

      define tick_next where \<open>tick_next = max MIN_TICK (min MAX_TICK tick_next')\<close> ;;
 
      if \<open>$tick_next < MIN_TICK\<close> \<medium_left_bracket>
        \<open>MIN_TICK\<close> \<rightarrow> tick_next
      \<medium_right_bracket> \<medium_left_bracket>
        if \<open>$tick_next > MAX_TICK\<close> \<medium_left_bracket> \<open>MAX_TICK\<close> \<rightarrow> tick_next \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
      \<medium_right_bracket> as \<open>tick_next \<Ztypecolon> Tick\<close>
 
      let ?growth' = \<open>growth + fee_growth zeroForOne fee_rate' L price pr\<close> ;;

      pure_fact [useful]: \<open>0 < pr\<close>
            and tick_next_dom: \<open>MIN_TICK \<le> tick_next\<close> \<open>tick_next \<le> MAX_TICK\<close>
      
      have y0: \<open>if j < tick_next' then next_initialized Lg j tick_next' else next_initialized Lg (tick_next') (j+1)\<close>
        by (auto, metis greaterThanLessThan_iff not_less_iff_gr_or_eq order_less_le_trans the_\<phi>(15) the_\<phi>lemmata(4),
                  metis dual_order.strict_trans1 greaterThanAtMost_iff order_less_le the_\<phi>(15) the_\<phi>lemmata(4)) ;;

      pure_fact \<open>if j < tick_next then next_initialized Lg j tick_next else next_initialized Lg tick_next (j+1)\<close>
            and x1: \<open>zeroForOne \<Longrightarrow> tick_next \<le> j\<close>
            and \<open>\<not> zeroForOne \<Longrightarrow> j < tick_next\<close>
            and t8: \<open>zeroForOne \<Longrightarrow> \<forall>k. tick_next < k \<and> k \<le> j \<longrightarrow> Lg k = 0\<close>
            and t8': \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. j < k \<and> k \<le> (tick_next - 1) \<longrightarrow> Lg k = 0\<close>

      have t7: \<open>\<And>k. zeroForOne \<Longrightarrow> tick_next \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> L k = L j\<close>
        subgoal premises Ps for k
          using t8 Ps(2) apply (induct rule: int_le_induct[where k=j and i=k, OF Ps(3)]; simp)
          by (metis Ps(1) the_\<phi>(14)) .

      have t11: \<open>\<And>k. \<not> zeroForOne \<Longrightarrow> k < tick_next \<Longrightarrow> j \<le> k \<Longrightarrow> L k = L j\<close>
        subgoal premises Ps for k
          using t8' Ps(2) apply (induct rule: int_ge_induct[where k=j and i=\<open>k\<close>, OF Ps(3)]; simp)
          using Ps(1) the_\<phi>(14) by fastforce . ;;

      getSqrtRatioAtTick ($tick_next) \<rightarrow> val step_price_next

      computeSwapStep (
        $price,
        sel ($price_limit, $step_price_next,
                sel (\<open>$step_price_next < $price_limit\<close>, \<open>$step_price_next > $price_limit\<close>, $zeroForOne))
         is \<open>if zeroForOne then max $step_price_next price_limit else min $step_price_next price_limit\<close>,
        $liquidity,
        $amount_remaining,
        fee
      ) \<exists>next_price, amountIn, amountOut, fee_amount
      \<rightarrow> price, val amountIn, amountOut, feeAmount ;;

      pure_fact d2: \<open>fee_amount = amountIn * fee_rate'\<close>

      have d1[simp]: \<open>amountIn + fee_amount = amountIn / (1 - fee_rate)\<close> by (smt (verit, ccfv_threshold) ab_semigroup_mult_class.mult_ac(1) add.commute add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel comm_semiring_class.distrib d2 diff_add_eq diff_diff_eq2 diff_zero div_by_1 divide_cancel_right divide_divide_eq_left divide_divide_eq_left' divide_divide_eq_right divide_eq_0_iff divide_real_def eq_divide_imp fee_rate_range linorder_not_le minus_diff_eq mult.commute mult.left_commute mult.right_neutral mult_1 mult_cancel_left2 mult_eq_0_iff mult_zero_left mult_zero_right nle_le nonzero_divide_mult_cancel_left nonzero_mult_div_cancel_left order_refl real_divide_square_eq right_diff_distrib' ring_class.ring_distribs(1) times_divide_eq_left fee_rate'_def) ;;
  
      pure_fact \<open>MIN_PRICE < (if zeroForOne then max $step_price_next price_limit else min $step_price_next price_limit)\<close>
            and \<open>MIN_PRICE < next_price\<close>
            and \<open>\<not> zeroForOne \<Longrightarrow> next_price < MAX_PRICE\<close>
            and \<open>zeroForOne \<Longrightarrow> next_price \<le> pr\<close> 
            and \<open>zeroForOne \<Longrightarrow> price_of tick_next \<le> next_price \<and> price_limit \<le> next_price\<close>
            and \<open>\<not> zeroForOne \<Longrightarrow> pr \<le> next_price\<close> 
            and \<open>\<not> zeroForOne \<Longrightarrow> next_price \<le> price_of tick_next \<and> next_price \<le> price_limit\<close>
            and \<open>zeroForOne \<Longrightarrow> \<forall>k. next_price \<le> k \<and> k < pr \<longrightarrow> L (tick_of_price k) = L j\<close>
            and \<open>\<not> zeroForOne \<Longrightarrow> \<forall>k. pr \<le> k \<and> k < next_price \<longrightarrow> L (tick_of_price k) = L j\<close>
            and p1: \<open>zeroForOne \<Longrightarrow> L (tick_of_price next_price) = L j\<close>
            and p2: \<open>if zeroForOne then (amountIn, amountOut) = reserve_change_in_a_step (L (tick_of_price next_price)) next_price pr
                               else (amountOut, amountIn) = reserve_change_in_a_step (L (tick_of_price pr)) pr next_price\<close>
            and pp2: \<open>\<not> zeroForOne \<Longrightarrow> amountIn = (next_price - pr) * L j\<close> 
        
        have pp1: \<open>zeroForOne \<Longrightarrow> amountIn = (1/next_price - 1/pr) * L j\<close>
          by (metis comm_monoid_mult_class.mult_1 divide_real_def growth.fee0 mult.commute p1 p2 reserve_change_in_a_step_def right_diff_distrib') ;;
        
      if $exactInput \<medium_left_bracket>
          \<open>$amount_remaining - ($amountIn + $feeAmount)\<close> \<rightarrow> amount_remaining
          \<open>$amount_calculated - $amountOut\<close> \<rightarrow> amount_calculated
      \<medium_right_bracket> \<medium_left_bracket>
          \<open>$amount_remaining + $amountOut\<close> \<rightarrow> amount_remaining
          \<open>$amount_calculated + ($amountIn + $feeAmount)\<close> \<rightarrow> amount_calculated
      \<medium_right_bracket>

      if \<open>$feeProtocol > 0\<close> \<medium_left_bracket>
        \<open>$feeAmount / real $feeProtocol\<close> \<rightarrow> val delta
        \<open>$feeAmount - $delta\<close> \<rightarrow> feeAmount
        \<open>$protocolFee + $delta\<close> \<rightarrow> protocolFee
      \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>

      define step_growth where \<open>step_growth = (if L j = 0 then 0 else fee_amount / L j)\<close>
      define \<Delta>growth where \<open>\<Delta>growth = fee_growth zeroForOne fee_rate' L pr next_price\<close> ;;

      pure_fact \<open>0 < L j \<Longrightarrow> zeroForOne \<Longrightarrow> global_fee0_growth (fee_growth' True fee_rate' L next_price pr) = (1/next_price - 1/pr) * fee_rate'\<close>
            and \<open>0 < L j \<Longrightarrow> \<not> zeroForOne \<Longrightarrow> global_fee1_growth (fee_growth' False fee_rate' L pr next_price) = (next_price - pr) * fee_rate'\<close> ;;

      if \<open>$liquidity > 0\<close> \<medium_left_bracket>
        \<open>$fee_growth_global + ($feeAmount / $liquidity)\<close> \<rightarrow> fee_growth_global
      \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
      is \<open>I_fee_growth_global (?growth' + \<Delta>growth)\<close> ;;

      define real_next_tick where \<open>real_next_tick = (if zeroForOne then tick_next - 1 else tick_next)\<close> 

      have real_next_tick_dom[simp]: \<open>real_next_tick \<in> {MIN_TICK - 1..MAX_TICK}\<close>
        using real_next_tick_def tick_next_dom(1) tick_next_dom(2) by force ;;

      if \<open>$price = $step_price_next\<close> \<medium_left_bracket>

        if $initialized \<medium_left_bracket>

          apply_rule tick_cross[where \<Delta>=\<Delta>growth] (

            $tick_next,

            sel ($fee_growth_global, \<open>growth.fee0 (pool.growth _)\<close>, $zeroForOne)
              is \<open>global_fee0_growth (?growth' + \<Delta>growth)\<close>

            sel (\<open>growth.fee1 (pool.growth _)\<close>, $fee_growth_global, $zeroForOne)
              is \<open>global_fee1_growth (?growth' + \<Delta>growth)\<close>
           )
           \<rightarrow> var liquidityNet ;;
            
            \<open>_ \<Ztypecolon> Ticks\<close> is \<open>(_,_, ?growth' + \<Delta>growth, real_next_tick,_)\<close>

            if $zeroForOne \<medium_left_bracket> \<open>- $liquidityNet\<close> \<rightarrow> liquidityNet \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> ;;
              
              \<open>$liquidity + $liquidityNet\<close> \<rightarrow> $liquidity is \<open>L real_next_tick\<close>

            \<medium_right_bracket> \<medium_left_bracket>

              \<open>\<v>\<a>\<r>[liquidity]\<close> is \<open>L real_next_tick\<close>

              apply_rule shift_current_tick_\<Delta>[where j=\<open>real_next_tick\<close> and \<Delta>=\<Delta>growth]
        \<medium_right_bracket>

        sel (
          \<open>$tick_next - 1\<close> to Tick,
          $tick_next,
          $zeroForOne
        )
        is \<open>real_next_tick\<close> \<rightarrow> tick

        pure_fact [simp]: \<open>real_next_tick < MAX_TICK\<close>

      \<medium_right_bracket> for \<open>_ \<s>\<u>\<b>\<j> real_next_tick < MAX_TICK\<close>
      \<medium_left_bracket>
        pure_fact \<open>  zeroForOne \<Longrightarrow> tick_of_price next_price \<le> j\<close> 
              and \<open>\<not> zeroForOne \<Longrightarrow> j \<le> tick_of_price next_price\<close>
              and \<open>  zeroForOne \<Longrightarrow> tick_next \<le> tick_of_price next_price\<close>
              and \<open>\<not> zeroForOne \<Longrightarrow> tick_of_price next_price < tick_next\<close>
              and \<open>L j = L (tick_of_price next_price)\<close> ;;

        if \<open>$price \<noteq> $step_price_start\<close> \<medium_left_bracket>
          getTickAtSqrtRatio ($price) \<rightarrow> tick
        \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> is \<open>tick_of_price next_price\<close> ;;

        \<open>\<v>\<a>\<r>[liquidity]\<close> is \<open>L (tick_of_price next_price)\<close>  ;;

        apply_rule shift_current_tick_\<Delta>[where j=\<open>tick_of_price next_price\<close> and \<Delta>=\<Delta>growth]
        
      \<medium_right_bracket>

      define real2_next_tick where
        \<open>real2_next_tick = (if next_price = price_of tick_next then real_next_tick else tick_of_price next_price)\<close> ;;

      \<open>\<v>\<a>\<r>[tick]\<close>      is  real2_next_tick ;;
      \<open>\<v>\<a>\<r>[liquidity]\<close> is \<open>L real2_next_tick\<close> ;;
      \<open>Ticks\<close> is \<open>(Lg, L, ?growth' + \<Delta>growth, real2_next_tick, \<delta>)\<close> ;;

      pure_fact Iv1: \<open>real2_next_tick < MAX_TICK\<close>
            and Iv2: \<open>MIN_PRICE \<le> next_price \<and> next_price < MAX_PRICE\<close>
            and Iv3: \<open>tick_of_price next_price = real2_next_tick \<or> next_price = price_of (real2_next_tick + 1)\<close>
            and Iv4: \<open>if zeroForOne then price_limit \<le> next_price \<and> next_price \<le> price
                                    else price \<le> next_price \<and> next_price \<le> price_limit\<close>
            and      \<open>if zeroForOne then Const_Interval (L o tick_of_price) next_price pr
                              else Const_Interval (L o tick_of_price) pr next_price\<close>
            and Iv6: \<open>if zeroForOne then reserve_change' L next_price price = (amountIn, amountOut) + reserve_change' L pr price
                                    else reserve_change' L price next_price = reserve_change' L price pr + (amountOut, amountIn)\<close>
            and Iv5: \<open>?growth' + \<Delta>growth = growth + fee_growth zeroForOne fee_rate' L price next_price\<close>
            

  \<medium_right_bracket> certified using \<open>let _ = _ in _\<close> Iv1 Iv2 Iv3 Iv4 Iv5 Iv6 by (auto simp add: d2 add_divide_distrib distrib_right) ;;
    
    \<exists>amount_remaining', price', amount_calculated', proto_fee', i' ;;

  set_pool_tick ($tick)
  set_pool_price ($price) ;;

  if \<open>$liquidityStart \<noteq> $liquidity\<close> \<medium_left_bracket> set_pool_liquidity ( $liquidity ) \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>
      is \<open>pool _ _ _ (L i') _ _ _\<close>

  pure_fact proto_fee': \<open>proto_fee' =
      (if 0 < fee_proto then ((if zeroForOne then fst else snd) (reserve_change zeroForOne L price price')) * fee_rate' / real fee_proto else 0)\<close>
    and proto_fee'_LE0: \<open>0 \<le> proto_fee'\<close> ;;

  if $zeroForOne \<medium_left_bracket>

    set_pool_fee_growth_0 ($fee_growth_global)
    is \<open>pool _ _ _ _ (gSum (growth + fee_growth zeroForOne fee_rate' L price price')) _ _\<close>
    certified by (auto simp add: prod_eq_iff growth.map_fee0_def I_fee_growth_global_def growth.fee0_def growth.fee1_def the_\<phi>(15)) (metis fee_growth_is_0_when_zeroForOne growth.fee1_def the_\<phi>(1) the_\<phi>(15) the_\<phi>(18)) ;;

    if \<open>$protocolFee > 0\<close> \<medium_left_bracket> set_pool_protocal_fee_0 (\<open>fst (pool.protocol_fees _) + $protocolFee\<close>) \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket>

   \<medium_right_bracket> \<medium_left_bracket>

    set_pool_fee_growth_1 ($fee_growth_global)
    is \<open>pool price' i' False (L i') (gSum (growth + fee_growth zeroForOne fee_rate' L price price')) fee_protocol protocol_fees\<close>
      certified by (auto simp add: prod_eq_iff growth.map_fee1_def I_fee_growth_global_def growth.fee0_def growth.fee1_def the_\<phi>(15)) (metis \<open>0 < price\<close> fee_growth_is_0_when_not_zeroForOne growth.fee0_def the_\<phi>(15) the_\<phi>(18))  ;;

    if \<open>$protocolFee > 0\<close> \<medium_left_bracket> set_pool_protocal_fee_1 (\<open>snd (pool.protocol_fees _) + $protocolFee\<close>) \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> ;;

  \<medium_right_bracket>
  is \<open>pool price' i' False (L i') (gSum (growth + fee_growth zeroForOne fee_rate' L price price')) fee_protocol
           (protocol_fees + \<Delta>protocal_fees fee_protocol zeroForOne L price price' fee_rate')\<close> 
  certified by (cases protocol_fees; auto simp add: \<Delta>protocal_fees_def fee_proto_def proto_fee' zero_prod_def,
                (insert fee_proto_def proto_fee' proto_fee'_LE0 zero_prod_def, fastforce)[1],
                (insert fee_proto_def proto_fee' proto_fee'_LE0 zero_prod_def, fastforce)[1],
                (insert fee_proto_def proto_fee' proto_fee'_LE0, force)[1],
                (insert fee_proto_def proto_fee' proto_fee'_LE0, fastforce)[1]) ;;

  if \<open>$zeroForOne = $exactInput\<close>
    \<medium_left_bracket> (\<open>$amount_specified - $amount_remaining\<close>, $amount_calculated) \<medium_right_bracket>
    \<medium_left_bracket> ($amount_calculated, \<open>$amount_specified - $amount_remaining\<close>) \<medium_right_bracket> \<rightarrow> val amount0, amount1
  
  $amount0 is \<open>if zeroForOne then fst (reserve_change' L price' price) / (1 - fee_rate)
                             else - fst (reserve_change' L price price')\<close>
           \<rightarrow> val amount0

  $amount1 is \<open>if zeroForOne then - snd (reserve_change' L price' price)
                             else snd (reserve_change' L price price') / (1 - fee_rate)\<close>
           \<rightarrow> val amount1

  if $zeroForOne \<medium_left_bracket>
    if \<open>$amount1 < 0\<close> \<medium_left_bracket> \<open>-$amount1\<close> \<medium_right_bracket> \<medium_left_bracket> \<open>0 \<Ztypecolon> \<real>\<close> \<medium_right_bracket>
    is \<open>snd (reserve_change' L price' price)\<close>

    $amount0 is \<open>fst (reserve_change' L price' price) / (1 - fee_rate)\<close>
  \<medium_right_bracket> \<medium_left_bracket>
    if \<open>$amount0 < 0\<close> \<medium_left_bracket> \<open>-$amount0\<close> \<medium_right_bracket> \<medium_left_bracket> \<open>0 \<Ztypecolon> \<real>\<close> \<medium_right_bracket>
    is \<open>fst (reserve_change' L price price')\<close>

    $amount1 is \<open>snd (reserve_change' L price price') / (1 - fee_rate)\<close>
  \<medium_right_bracket>

  set_pool_unlock (True)

\<medium_right_bracket>.

end 

end