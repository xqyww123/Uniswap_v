theory Uniswap_v_Report
  imports Uniswap_v_Report_helpers
begin

section \<open>Introduction\<close>

text \<open>The formalization given in this verification project is based on the Uniswap v3 whitepaper.

The contract system contains 3 major modules,
\<^item> Swapping for exchanging tokens
\<^item> Burn \& Mint for providing and withdrawing liquidity
\<^item> Observation for recording historical changes of the price.

To the date of the document, only the first module is specified and partially verified.
\<close>

section \<open>Specifying the swap operation\<close>

text \<open>
The key concept of the swapping module is the correspondence between reserves of the two tokens,
  the price, and the liquidity.\<close>

subsection \<open>Specifying relationship between reserves, price, and liquidity\<close>

text \<open>
A key novelty of Uniswap v3 is \<^emph>\<open>virtual liquidity\<close>. Liquidity providers can limit their liquidity
in a price interval so the amount of liquidity can be different at different price, making it a real
function of price.

To implement this, Uniswap discretizes the real function by splitting the price domain into many
intervals named \<^emph>\<open>ticks\<close>, which are the minimal resolution unit of the price intervals of liquidity,
so liquidity is constant in every tick.

We formalize the conversion between prices and (lower bound of) ticks by \<^const>\<open>price_of\<close> and \<^const>\<open>tick_of_price\<close>,
and lemmas @{thm price_of_tick} @{thm tick_of_price}.

When the liquidity is constant in a price interval, the relation between the reserves and the price
can be given, as the formula (6.16) and (6.13) in the whitepaper.

\<open>\<Delta>x = \<Delta>(1 / sqrt(P)) * L      \<Delta>y = \<Delta>(sqrt(P)) * L\<close>

We formalize this by \<^term>\<open>reserve_change_in_a_step L\<^sub>0 p\<^sub>0 p\<^sub>1\<close> which gives the change of
the reserves of the token0 and the token1 respectively when the price moves from \<open>p\<^sub>0\<close> to \<open>p\<^sub>1\<close>,
and when the liquidity between the prices is constant \<open>L\<^sub>0\<close>.
\<close>

lemma reserve_change_in_a_step__definition:
  \<open>reserve_change_in_a_step L\<^sub>0 p\<^sub>0 p\<^sub>1 = (L\<^sub>0 / p\<^sub>0 - L\<^sub>0 / p\<^sub>1, L\<^sub>0 * (p\<^sub>1 - p\<^sub>0))\<close>
  using reserve_change_in_a_step_def .

text \<open>As the liquidity between two arbitrary prices is not necessarily a constant but a function of
the price, the reserve change between the two prices is the integral over the prices, namely,
by splitting the price interval into several partitions in every of which the liquidity is constant,
the sum of the evaluation of the every partition.

We formalize this by \<^const>\<open>Const_Interval\<close>, \<^const>\<open>Is_partition\<close>, and \<^const>\<open>partition_integral\<close>.
\<close>

lemma Const_Interval__definition:
  \<open>Const_Interval L\<^sub>p l u \<longleftrightarrow> l \<le> u \<and> (\<forall>k. l \<le> k \<and> k < u \<longrightarrow> L\<^sub>p k = L\<^sub>p l)\<close>
  unfolding Const_Interval_def by (smt (verit, best)) 

text \<open>\<^term>\<open>L\<^sub>p :: price \<Rightarrow> liquidity\<close> is the function from prices to their liquidity.
Predicate \<^term>\<open>Const_Interval L\<^sub>p l u\<close> specifies \<open>[l,u)\<close> is a price interval where the liquidity
on the prices is constant.\<close>

lemma Is_partition__definition:
  \<open>Is_partition L\<^sub>p l u [] \<longleftrightarrow> Const_Interval L\<^sub>p l u\<close>
  \<open>Is_partition L\<^sub>p l u ([h] @ r) \<longleftrightarrow> Const_Interval L\<^sub>p l h \<and> Is_partition L\<^sub>p h u r\<close>
  by simp+

text \<open>We use an order list (a chain) to represent a partition, e.g. \<^term>\<open>[x\<^sub>0,x\<^sub>1,x\<^sub>2]\<close> for \<open>[l,x\<^sub>0), [x\<^sub>0,x\<^sub>1), [x\<^sub>1,x\<^sub>2), [x\<^sub>2,u)\<close>.
Predicate \<open>Is_partition f l u ps\<close> asserts if \<open>ps\<close> is a valid partition where every interval has constant liquidity.

Then, we can add up the evaluation of every partition to get the integral, by a recursion function as the following.
\<close>

lemma partition_intergral__definition:
  \<open>partition_integral reserve_change_in_a_step L\<^sub>p low up []
      = reserve_change_in_a_step (L\<^sub>p low) low up\<close>
  \<open>partition_integral reserve_change_in_a_step L\<^sub>p low up ([h] @ r)
      = reserve_change_in_a_step (L\<^sub>p low) low h + partition_integral reserve_change_in_a_step L\<^sub>p h up r\<close>
  by simp+


text \<open>Finally, we can specify the relationship between reserves, price, and liquidity,
  which is the integral following any valid partition.\<close>

lemma
\<open>reserve_change' L lower upper
    = partition_integral reserve_change_in_a_step (L \<circ> tick_of_price) lower upper
                          (SOME ps. Is_partition (L \<circ> tick_of_price) lower upper ps)\<close>
  by (metis Eps_cong Is_key_partition_implies_Is_partition reserve_change'_def reserve_change_irrelavent_with_partition someI_ex)

text \<open>\<^term>\<open>L :: tick \<Rightarrow> liquidity\<close> is the function from ticks to their liquidity.
There is \<open>L \<circ> tick_of_price \<equiv> L\<^sub>p\<close>.
By lemma @{thm partition_intergral_irrelavent_with_parition}, the result of the integral is irrelavent
with specific partitions.\<close>

text \<open>Now we can specify the swap operation of Uniswap.\<close>

subsection \<open>Specifying swap operation\<close>

lemma (in Pool)
 \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> 0 \<noteq> amount_specified \<and> 0 < price_limit \<Longrightarrow>
  \<p>\<r>\<e>\<m>\<i>\<s>\<e> unlocked \<Longrightarrow>
  \<p>\<r>\<e>\<m>\<i>\<s>\<e> (if zeroForOne then price_limit < price \<and> MIN_PRICE < price_limit else price < price_limit \<and> price_limit < MAX_PRICE) \<Longrightarrow>

  \<p>\<r>\<o>\<c> swap (\<a>\<r>\<g>3 \<^bold>, \<a>\<r>\<g>2 \<^bold>, \<a>\<r>\<g>1)
  \<lbrace> (price, i, unlocked, Lg, L, growth, \<delta>, fee_protocol, protocol_fees) \<Ztypecolon> Uniswap_Pool\<heavy_comma>
     zeroForOne \<Ztypecolon> \<v>\<a>\<l>[\<a>\<r>\<g>1] \<bool>\<heavy_comma> amount_specified \<Ztypecolon> \<v>\<a>\<l>[\<a>\<r>\<g>2] \<real>\<heavy_comma> price_limit \<Ztypecolon> \<v>\<a>\<l>[\<a>\<r>\<g>3] \<real>
  \<longmapsto>
   (price', i', unlocked, Lg, L, growth + fee_growth zeroForOne fee_rate' L price price', \<delta>, fee_protocol,
       protocol_fees + \<Delta>protocal_fees fee_protocol zeroForOne L price price' fee_rate') \<Ztypecolon> Uniswap_Pool\<heavy_comma>
     transfer_out \<Ztypecolon> \<v>\<a>\<l> \<real>\<heavy_comma> transfer_in \<Ztypecolon> \<v>\<a>\<l> \<real>
   \<s>\<u>\<b>\<j> price' i' transfer_out transfer_in.
     (if zeroForOne then price_limit \<le> price' else price' \<le> price_limit) \<and>
     (price' = price_limit \<or>
      (if 0 < amount_specified then amount_specified * (1 - fee_rate) = (if zeroForOne then fst else snd) (reserve_change zeroForOne L price price')
       else - amount_specified = (if zeroForOne then snd else fst) (reserve_change zeroForOne L price price'))) \<and>
     transfer_out = (if zeroForOne then snd else fst) (reserve_change zeroForOne L price price') \<and>
     transfer_in = (if zeroForOne then fst else snd) (reserve_change zeroForOne L price price') / (1 - fee_rate)
  \<rbrace>\<close>
  using swap_\<phi>app .

text \<open>Right now we have only verified the operation works correctly when the input arguments are valid as
  specified in the three leading premises. When our underlying verification platform is completed,
  we can in addition show a state revert would happen on invalid arguments so completes
  this verification.

The proof is given by theorem @{thm Uniswap_Pool.Pool.swap_\<phi>app}.

Argument \<^term>\<open>zeroForOne\<close> indicates if the user wants to buy token1 using token0 or reversely to buy
token1 using token0.
\<^term>\<open>amount_specified\<close> is the amount that the user wants to pay if it is positive,
or the amount that user wants to pay for if it is negative.
As the transaction affects the price, the transaction terminates once the price reaches the \<^term>\<open>price_limit\<close>
or all the specified amount is processed.

The initial state of the Uniswap pool contract is on price \<^term>\<open>price\<close>, tick \<^term>\<open>i\<close>, liquidity \<^term>\<open>L\<close>.
\<^term>\<open>growth :: tick \<Rightarrow> fee \<times> fee\<close> is the function from ticks to transaction fees that have been
gained on the tick, in earning per unit of liquidity and for token0 and token1 respectively.
Liquidity providers' yields are calculated by multiplying it by the amount of their liquidity.
\<^term>\<open>fee_protocol\<close> is the proportion of the contract owner's commission from the transaction fee.
\<^term>\<open>protocol_fees\<close> is the amount of the contract owner's commission that has been gained.

\<^term>\<open>Lg\<close> is a technical scaffold used in the implementation. So-called \<^emph>\<open>Gross Liquidity\<close>, it is
a function from ticks to the total amount of liquidity providers' intervals that reference the tick.

The above lemma specifies, after execution of the swap operation, the resulted price \<^term>\<open>price'\<close>
will either reaches the \<^term>\<open>price_limit\<close> (but never exceeds it), or, is exactly the one causing
that the reserve change equals the specified amount, with transaction fee considered.
\<open>reserve_change zeroForOne L price next_price \<equiv> (if zeroForOne then reserve_change' L next_price price else reserve_change' L price next_price)\<close>
\<^term>\<open>reserve_change\<close> is precisely the \<^term>\<open>reserve_change'\<close> defined above but just considers the
order of the prices (buying token1 using token0 causes the price decreases and reversely for the other side).

The amount \<^term>\<open>transfer_in\<close> that the user needs to pay and \<^term>\<open>transfer_out\<close> that Uniswap transfers to the user
are the change of the reserves, with consideration of transaction fee.

\<^const>\<open>fee_rate\<close> is the rate of the transaction fee.
The record of the transaction fees is increased by \<open>fee_growth zeroForOne fee_factor L price price'\<close>
which gives for each tick the the fee per liquidity of the transaction moving the price from \<^term>\<open>price\<close> to \<^term>\<open>price'\<close>.
Note both \<^term>\<open>growth\<close> and \<^term>\<open>fee_growth zeroForOne fee_factor L price price'\<close> are functions of ticks,
and the addition is defined pointwisely.
\<^term>\<open>\<Delta>protocal_fees fee_protocol zeroForOne L price price' fee_factor\<close> gives the fee of
the contract owner's commission accordingly.

To conclude, we have verified the proper behavior of the swap operation under valid input arguments.
The implementation is highly optimized, and our proof recoveries from it the abstract liquidity distribution
and the fee-growth distribution as a close formalization of the white paper specification, showing
the implementation refines properly the white paper specification.

We haven't considered arithmetic overflow and precision error of fix-point arithmetic.
The verification is done on an abstract specification level where we use variables instead of
the exact solidity semantics to formalize the program.
We will keep developing our framework to cover the complete Uniswap modules, complete argument domain,
and concrete solidity semantics.
\<close>

end