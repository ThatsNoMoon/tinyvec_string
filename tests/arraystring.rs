use tinyvec::ArrayVec;
use tinyvec_string::arraystring::*;

use std::{borrow::Cow, convert::TryInto};

#[test]
fn test_from_str() {
	let owned: Option<ArrayString<[u8; 16]>> = "string".parse().ok();
	assert_eq!(owned.as_ref().map(|s| &**s), Some("string"));

	let failure: Option<ArrayString<[u8; 4]>> = "string".parse().ok();
	assert_eq!(failure, None);
}

#[test]
fn test_from_cow_str() {
	assert_eq!(
		ArrayString::<[u8; 16]>::from(Cow::Borrowed("string")),
		"string"
	);
	assert_eq!(
		ArrayString::<[u8; 16]>::from(Cow::Owned(String::from("string"))),
		"string"
	);
}

#[test]
fn test_unsized_try_into() {
	let s: &str = "abc";
	let _: Result<ArrayString<[u8; 3]>, _> = (*s).try_into();
}

#[test]
fn test_from_utf8() {
	let xs: ArrayVec<[u8; 16]> = b"hello".iter().copied().collect();

	assert_eq!(
		ArrayString::from_utf8(xs).unwrap(),
		ArrayString::<[u8; 16]>::from("hello")
	);

	let s = "ศไทย中华Việt Nam".as_bytes();
	let mut xs = [0u8; 32];
	xs[..s.len()].copy_from_slice(s);
	let xs = ArrayVec::from_array_len(xs, s.len());

	assert_eq!(
		ArrayString::from_utf8(xs).unwrap(),
		ArrayString::<[u8; 32]>::from("ศไทย中华Việt Nam")
	);

	let s = b"hello\xFF";
	let mut xs = [0u8; 16];
	xs[..s.len()].copy_from_slice(s);
	let xs = ArrayVec::from_array_len(xs, s.len());

	let err = ArrayString::from_utf8(xs).unwrap_err();
	assert_eq!(err.as_bytes(), b"hello\xff");
	let err_clone = err.clone();
	assert_eq!(err, err_clone);

	let mut xs = [0u8; 16];
	xs[..s.len()].copy_from_slice(s);
	let xs = ArrayVec::from_array_len(xs, s.len());

	assert_eq!(err.into_bytes(), xs);
	assert_eq!(err_clone.utf8_error().valid_up_to(), 5);
}

#[test]
fn test_push_bytes() {
	let mut s = ArrayString::<[u8; 16]>::from("ABC");
	unsafe {
		let mv = s.as_mut_vec();
		mv.extend_from_slice(&[b'D']);
	}
	assert_eq!(s, "ABCD");
}

#[test]
fn test_push_str() {
	let mut s = ArrayString::<[u8; 64]>::new();
	s.push_str("");
	assert_eq!(&s[0..], "");
	s.push_str("abc");
	assert_eq!(&s[0..], "abc");
	s.push_str("ประเทศไทย中华Việt Nam");
	assert_eq!(&s[0..], "abcประเทศไทย中华Việt Nam");
}

#[test]
fn test_add_assign() {
	let mut s = ArrayString::<[u8; 64]>::new();
	s += "";
	assert_eq!(s.as_str(), "");
	s += "abc";
	assert_eq!(s.as_str(), "abc");
	s += "ประเทศไทย中华Việt Nam";
	assert_eq!(s.as_str(), "abcประเทศไทย中华Việt Nam");
}

#[test]
fn test_push() {
	let mut data = ArrayString::<[u8; 64]>::new();
	data.push_str("ประเทศไทย中");
	data.push('华');
	data.push('b'); // 1 byte
	data.push('¢'); // 2 byte
	data.push('€'); // 3 byte
	data.push('𤭢'); // 4 byte
	assert_eq!(data, "ประเทศไทย中华b¢€𤭢");
}

#[test]
fn test_pop() {
	let mut data = ArrayString::<[u8; 64]>::new();
	data.push_str("ประเทศไทย中华b¢€𤭢");
	assert_eq!(data.pop().unwrap(), '𤭢'); // 4 bytes
	assert_eq!(data.pop().unwrap(), '€'); // 3 bytes
	assert_eq!(data.pop().unwrap(), '¢'); // 2 bytes
	assert_eq!(data.pop().unwrap(), 'b'); // 1 bytes
	assert_eq!(data.pop().unwrap(), '华');
	assert_eq!(data, "ประเทศไทย中");
}

#[test]
fn test_split_off_empty() {
	let orig = "Hello, world!";
	let mut split = ArrayString::<[u8; 16]>::from(orig);
	let empty: ArrayString<[u8; 16]> = split.split_off(orig.len());
	assert!(empty.is_empty());
}

#[test]
#[should_panic]
fn test_split_off_past_end() {
	let orig = "Hello, world!";
	let mut split = ArrayString::<[u8; 16]>::from(orig);
	let _ = split.split_off(orig.len() + 1);
}

#[test]
#[should_panic]
fn test_split_off_mid_char() {
	let mut orig = ArrayString::<[u8; 16]>::from("山");
	let _ = orig.split_off(1);
}

#[test]
fn test_split_off_ascii() {
	let mut ab = ArrayString::<[u8; 16]>::from("ABCD");
	let cd = ab.split_off(2);
	assert_eq!(ab, "AB");
	assert_eq!(cd, "CD");
}

#[test]
fn test_split_off_unicode() {
	let mut nihon = ArrayString::<[u8; 16]>::from("日本語");
	let go = nihon.split_off("日本".len());
	assert_eq!(nihon, "日本");
	assert_eq!(go, "語");
}

#[test]
fn test_str_truncate() {
	let mut s = ArrayString::<[u8; 16]>::from("12345");
	s.truncate(5);
	assert_eq!(s, "12345");
	s.truncate(3);
	assert_eq!(s, "123");
	s.truncate(0);
	assert_eq!(s, "");

	let mut s = ArrayString::<[u8; 16]>::from("12345");
	let p = s.as_ptr();
	s.truncate(3);
	s.push_str("6");
	let p_ = s.as_ptr();
	assert_eq!(p_, p);
}

#[test]
fn test_str_truncate_invalid_len() {
	let mut s = ArrayString::<[u8; 16]>::from("12345");
	s.truncate(6);
	assert_eq!(s, "12345");
}

#[test]
#[should_panic]
fn test_str_truncate_split_codepoint() {
	let mut s = ArrayString::<[u8; 16]>::from("\u{FC}"); // ü
	s.truncate(1);
}

#[test]
fn test_str_clear() {
	let mut s = ArrayString::<[u8; 16]>::from("12345");
	s.clear();
	assert_eq!(s.len(), 0);
	assert_eq!(s, "");
}

#[test]
fn test_str_add() {
	let a = ArrayString::<[u8; 16]>::from("12345");
	let b = a + "2";
	let b = b + "2";
	assert_eq!(b.len(), 7);
	assert_eq!(b, "1234522");
}

#[test]
fn remove() {
	let mut s = ArrayString::<[u8; 64]>::from("ศไทย中华Việt Nam; foobar");
	assert_eq!(s.remove(0), 'ศ');
	assert_eq!(s.len(), 33);
	assert_eq!(s, "ไทย中华Việt Nam; foobar");
	assert_eq!(s.remove(17), 'ệ');
	assert_eq!(s, "ไทย中华Vit Nam; foobar");
}

#[test]
#[should_panic]
fn remove_bad() {
	ArrayString::<[u8; 16]>::from("ศ").remove(1);
}

#[test]
fn test_retain() {
	let mut s = ArrayString::<[u8; 16]>::from("α_β_γ");

	s.retain(|_| true);
	assert_eq!(s, "α_β_γ");

	s.retain(|c| c != '_');
	assert_eq!(s, "αβγ");

	s.retain(|c| c != 'β');
	assert_eq!(s, "αγ");

	s.retain(|c| c == 'α');
	assert_eq!(s, "α");

	s.retain(|_| false);
	assert_eq!(s, "");
}

#[test]
fn insert() {
	let mut s = ArrayString::<[u8; 32]>::from("foobar");
	let mut bits = [0; 4];
	let bits = 'ệ'.encode_utf8(&mut bits).as_bytes();
	println!("self len: {}; bytes len: {}", s.len(), bits.len());
	s.insert(0, 'ệ');
	assert_eq!(s, "ệfoobar");
	let mut bits = [0; 4];
	let bits = 'ย'.encode_utf8(&mut bits).as_bytes();
	println!("self len: {}; bytes len: {}", s.len(), bits.len());
	s.insert(6, 'ย');
	assert_eq!(s, "ệfooยbar");
}

#[test]
#[should_panic]
fn insert_bad1() {
	ArrayString::<[u8; 16]>::new().insert(1, 't');
}
#[test]
#[should_panic]
fn insert_bad2() {
	ArrayString::<[u8; 16]>::from("ệ").insert(1, 't');
}

#[test]
fn test_slicing() {
	let s = ArrayString::<[u8; 16]>::from("foobar");
	assert_eq!("foobar", &s[..]);
	assert_eq!("foo", &s[..3]);
	assert_eq!("bar", &s[3..]);
	assert_eq!("oob", &s[1..4]);
}

#[test]
fn test_from_iterator() {
	let s = ArrayString::<[u8; 64]>::from("ศไทย中华Việt Nam");
	let t = "ศไทย中华";
	let u = "Việt Nam";

	let a: String = s.chars().collect();
	assert_eq!(s, a);

	let mut b = ArrayString::<[u8; 64]>::from(t);
	b.extend(u.chars());
	assert_eq!(s, b);

	let mut c = ArrayString::<[u8; 128]>::new();
	c.extend(vec![t, u]);
	assert_eq!(s, c);

	let mut d = ArrayString::<[u8; 64]>::from(t);
	d.extend(vec![u]);
	assert_eq!(s, d);
}

#[test]
fn test_drain() {
	let mut s = ArrayString::<[u8; 16]>::from("αβγ");
	assert_eq!(s.drain(2..4).collect::<ArrayString<[u8; 16]>>(), "β");
	assert_eq!(s, "αγ");

	let mut t = ArrayString::<[u8; 16]>::from("abcd");
	t.drain(..0);
	assert_eq!(t, "abcd");
	t.drain(..1);
	assert_eq!(t, "bcd");
	t.drain(3..);
	assert_eq!(t, "bcd");
	t.drain(..);
	assert_eq!(t, "");
}

#[test]
fn test_replace_range() {
	let mut s = ArrayString::<[u8; 16]>::from("Hello, world!");
	s.replace_range(7..12, "世界");
	assert_eq!(s, "Hello, 世界!");
}

#[test]
#[should_panic]
fn test_replace_range_char_boundary() {
	let mut s = ArrayString::<[u8; 16]>::from("Hello, 世界!");
	s.replace_range(..8, "");
}

#[test]
fn test_replace_range_inclusive_range() {
	let mut v = ArrayString::<[u8; 8]>::from("12345");
	v.replace_range(2..=3, "789");
	assert_eq!(v, "127895");
	v.replace_range(1..=2, "A");
	assert_eq!(v, "1A895");
}

#[test]
#[should_panic]
fn test_replace_range_out_of_bounds() {
	let mut s = ArrayString::<[u8; 8]>::from("12345");
	s.replace_range(5..6, "789");
}

#[test]
#[should_panic]
fn test_replace_range_inclusive_out_of_bounds() {
	let mut s = ArrayString::<[u8; 8]>::from("12345");
	s.replace_range(5..=5, "789");
}

#[test]
fn test_replace_range_empty() {
	let mut s = ArrayString::<[u8; 8]>::from("12345");
	s.replace_range(1..2, "");
	assert_eq!(s, "1345");
}

#[test]
fn test_replace_range_unbounded() {
	let mut s = ArrayString::<[u8; 8]>::from("12345");
	s.replace_range(.., "");
	assert_eq!(s, "");
}

#[test]
fn test_extend_ref() {
	let mut a = ArrayString::<[u8; 16]>::from("foo");
	a.extend(&['b', 'a', 'r']);

	assert_eq!(&a, "foobar");
}

#[test]
fn test_from_char() {
	assert_eq!(ArrayString::<[u8; 16]>::from('a'), 'a'.to_string());
	let s: ArrayString<[u8; 16]> = 'x'.try_into().unwrap();
	assert_eq!(s, 'x'.to_string());
	assert_eq!(s, ArrayString::<[u8; 4]>::from_char_infallible('x'));
}
