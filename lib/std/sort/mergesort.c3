module std::sort;

<*
 Sort list using the mergesort algorithm.

 @require @list_is_by_ref(list) : "Expected a list passed by reference, or slice passed by value"
 @require @is_sortable(list) : "The list must be indexable and support .len or .len()"
 @require @is_valid_cmp_fn(#cmp: ...cmp, #list: list, #context: ...context) : "Expected a comparison function which compares values"
 @require @is_valid_context(...cmp, ...context) : "Expected a valid context"

 @param list : "The list to sort"
 @param cmp : "The comparison function"
 @param context : "The context to use with the comparion function as needed"
 @param buffer_allocator : "The allocator to use for allocating a buffer used by merge. Defaults to tmem."
*>
macro void mergesort(list, cmp = ..., context = ..., buffer_allocator = tmem) @builtin
{
	var used_cmp = $defined(cmp) ??? cmp : (TypeNotSet)null;
	var used_ctx = $defined(context) ??? context : (TypeNotSet)null;
	$if @kindof(list) == SLICE:
		msort{$typeof(list), $typeof(used_cmp), $typeof(used_ctx)}(list, used_cmp, used_ctx, buffer_allocator);
	$else
		msort{$typeof(*list), $typeof(used_cmp), $typeof(used_ctx)}(list, used_cmp, used_ctx, buffer_allocator);
	$endif
}

macro void mergesorti(list, cmp = ..., context = ...) @builtin
{
	var used_cmp = $defined(cmp) ??? cmp : (TypeNotSet)null;
	var used_ctx = $defined(context) ??? context : (TypeNotSet)null;
	$if @kindof(list) == SLICE:
		msorti{$typeof(list), $typeof(used_cmp), $typeof(used_ctx)}(list, used_cmp, used_ctx);
	$else
		msorti{$typeof(*list), $typeof(used_cmp), $typeof(used_ctx)}(list, used_cmp, used_ctx);
	$endif
}

module std::sort <Type, CmpFn, Context> @private;

// Inplace mergesort algorithm adapted from DOI: https://doi.org/10.48550/arXiv.2509.24540

fn void msorti(ListType list, CmpFn cmp, Context context)
{
	const LIST_IS_REF = @kindof(list) == POINTER;
	sz len = !LIST_IS_REF ??? lengthof(list) : lengthof(*list);
	if (len <= 1) return;
	msorti_split(list[..], cmp, context);
	return;
}

fn void msort(ListType list, CmpFn cmp, Context context, Allocator allocator)
{
	const LIST_IS_REF = @kindof(list) == POINTER;
	sz len = !LIST_IS_REF ??? lengthof(list) : lengthof(*list);
	if (len <= 1) return;
	ElementType[] buff = alloc::new_array(allocator, ElementType, len);
	msort_split(list, buff, 0, len, cmp, context);
	alloc::free(allocator, buff);
	return;
}

fn void msorti_split(ElementType[] a, CmpFn cmp, Context context)
{
	if (a.len <= 1) return;
	sz mid = a.len / 2;
	msorti_split(a[..mid - 1], cmp, context);
	msorti_split(a[mid..], cmp, context);
	merge_inplace(a, mid, a.len - mid, cmp, context);
}

<*
@require left <= right : "Indexing has to be done from lower to higher index"
*>
fn void msort_split(ListType list, ElementType[] buff, sz left, sz right, CmpFn cmp, Context context)
{
	if (right - left <= 1) return;
	sz mid = left + (right - left) / 2;
	msort_split(list, buff, left, mid, cmp, context);
	msort_split(list, buff, mid, right, cmp, context);
	merge(list, buff, left, mid, right, cmp, context);
}

<*
@require left <= mid : "Indexing has to be done from lower to higher index"
@require mid <= right : "Indexing has to be done from lower to higher index"
*>
fn void merge(ListType list, ElementType[] buff, sz left, sz mid, sz right, CmpFn cmp, Context context)
{
	var $has_cmp = $typeof(cmp) != TypeNotSet;
	var $has_context = $typeof(context) != TypeNotSet;
	var $cmp_by_value = $has_cmp &&& $defined($typefrom(CmpFn::params[0].type) v = list_get(list, 0));

	sz i = left;
	sz j = mid;
	sz k = left;
	while(i < mid && j < right){
		$switch:
			$case $cmp_by_value && $has_context:
				bool cmp_result = cmp(list_get(list, i), list_get(list, j), context) <= 0;
			$case $cmp_by_value:
				bool cmp_result = cmp(list_get(list, i), list_get(list, j)) <= 0;
			$case $has_cmp && $has_context:
				bool cmp_result = cmp(list_get_ref(list, i), list_get_ref(list, j), context) <= 0;
			$case $has_cmp:
				bool cmp_result = cmp(list_get_ref(list, i), list_get_ref(list, j)) <= 0;
			$default:
				bool cmp_result = less_eq(list_get(list, i), list_get(list, j));
		$endswitch
		if (cmp_result)
		{
			buff[k++] = list_get(list, i++);
		}
		else
		{
			buff[k++] = list_get(list, j++);
		}
	}

	while (i < mid) buff[k++] = list_get(list, i++);
	while (j < right) buff[k++] = list_get(list, j++);
	mem::copy(list_get_ref(list, left), &buff[left], (right - left) * @sizeof(list_get(list, 0)));
}

import std::math;

fn void rotate(sz offset, ElementType[] a)
{
	if (a.len <= 0 || offset <= 0) return;

	sz i, next;
	ElementType first;

	sz work = a.len;
	for (sz s = 0; work > 0; s++)
	{
		i = s;
		first = list_get(a, s);
		do
		{
			next = i + offset;
			if (next >= a.len) next -= a.len;
			if (next == s) 
			{
				list_set(a, i, first);
			}
			else
			{
				list_set(a, i, list_get(a, next));
			}
			i = next;
			work--;
		}
		while (i != s);
	}
}

macro compare(list_a, list_b, a, b, cmp, context)
{
	var $has_cmp = $typeof(cmp) != TypeNotSet;
	var $has_context = $typeof(context) != TypeNotSet;
	var $cmp_by_value = $has_cmp &&& $defined($typefrom(CmpFn::params[0].type) v = list_get(list_a, 0));

	$switch:
		$case $cmp_by_value && $has_context:
			return cmp(list_get(list_a, a), list_get(list_b, b), context);
		$case $cmp_by_value:
			return cmp(list_get(list_a, a), list_get(list_b, b));
		$case $has_cmp && $has_context:
			return cmp(list_get_ref(list_a, a), list_get_ref(list_b, b), context);
		$case $has_cmp:
			return cmp(list_get_ref(list_a, a), list_get_ref(list_b, b));
		$default:
			return compare_to(list_get(list_a, a), list_get(list_b, b));
	$endswitch
}

fn sz[2] co_rank(sz i, ElementType[] a, ElementType[] b, CmpFn cmp, Context context)
{
	sz j, k, j_low, k_low;
	j = math::min(i, a.len);
	k = i - j;
	j_low = math::max((sz)0, i - b.len);

	while(true)
	{
		if (j > 0 && k < b.len && compare(a, b, j - 1, k, cmp, context) > 0)
		{
			sz delta = (1 + j - j_low) / 2;
			k_low = k;
			j -= delta;
			k += delta;
		}
		else if (k > 0 && j < a.len && compare(b, a, k - 1, j, cmp, context) >= 0)
		{
			sz delta = (1 + k - k_low) / 2;
			j_low = j;
			j += delta;
			k -= delta;
		}
		else
		{
			return {j, k};
		}
	}
}

fn void merge_inplace(ElementType[] a, sz index, sz len, CmpFn cmp, Context context)
{
	if (index <= 0 || len <= 0) return;

	ElementType[] b, m;

	b = a[index:len];
	
	sz[2] j_k = co_rank(index, a, b, cmp, context);
	m = a[j_k[0]:(index - j_k[0]) + j_k[1]];
	rotate(j_k[1], m);
	merge_inplace(a, j_k[0], index - j_k[0], cmp, context);
	merge_inplace(b, j_k[1], len - j_k[1], cmp, context);
}