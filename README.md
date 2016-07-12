# Regular Expression Derivatives in Scheme

A regular expression engine based on regular expression derivatives. In particular, this engine is based on the paper
"[Regular-expression derivatives reexamined](http://www.ccs.neu.edu/home/turon/re-deriv.pdf)"
by Scott Owens, John Reppy, and Aaron Turon; and the work by Matt Might, such as
[Parsing regular expressions with recursive descent](http://matt.might.net/articles/parsing-regex-with-recursive-descent/).

Currently, this library implements `string->dre` and `dre-match?`

```scheme
> (string->dre "a.(b|c)")
$73 = #<dre-concat-t left: #<dre-chars-t positive: #t chars: (#\a)>
right: #<dre-concat-t left: #<dre-chars-t positive: #f chars: (#\newline)>
right: #<dre-or-t left: #<dre-chars-t positive: #t chars: (#\b)>
right: #<dre-chars-t positive: #t chars: (#\c)>>>>
> (dre-match? (string->dre "a.b") "anb")
$74 = #t
```

I am using Guile, which is rather a pity since if I were using Racket I could have called this thing "Dr. DRE."
