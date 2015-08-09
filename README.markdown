Tables
======

[![Hackage](https://img.shields.io/hackage/v/tables.svg)](https://hackage.haskell.org/package/tables) [![Build Status](https://secure.travis-ci.org/ekmett/tables.png?branch=master)](http://travis-ci.org/ekmett/tables

This package provides simple in memory data tables with multiple indices.

Examples
--------

So if we load `examples/Foo.hs` into `ghci`, we start with:

```haskell
>>> test
fromList [ Foo {fooId = 1, fooBar = "One", fooBaz = 1.0}
         , Foo {fooId = 2, fooBar = "Two", fooBaz = 2.0}
         , Foo {fooId = 3, fooBar = "Three", fooBaz = 3.0}
         , Foo {fooId = 4, fooBar = "Four", fooBaz = 4.0}
         , Foo {fooId = 5, fooBar = "Five", fooBaz = 5.0} ]
```

We use uppercase constructor names to match on built-in keys

```haskell
>>> test ^. with FooId (<) 3
fromList [ Foo {fooId = 1, fooBar = "One", fooBaz = 1.0}
         , Foo {fooId = 2, fooBar = "Two", fooBaz = 2.0} ]
```

Then we can use any lowercase field accessor (or any other function) to do a non-keyed lookup or filter

```haskell
>>> test ^. with (length . fooBar) (<=) 3
fromList [ Foo {fooId = 1, fooBar = "One", fooBaz = 1.0}
         , Foo {fooId = 2, fooBar = "Two", fooBaz = 2.0} ]
```

You can delete by assigning to that filtered table:

```haskell
>>> test & with (length . fooBar) (<=) 3 .~ empty
fromList [ Foo {fooId = 3, fooBar = "Three", fooBaz = 3.0}
         , Foo {fooId = 4, fooBar = "Four", fooBaz = 4.0}
         , Foo {fooId = 5, fooBar = "Five", fooBaz = 5.0} ]
```

You can edit the actual type of the fields if the table is configured to allow it:

```haskell
>>> test & rows.fooBar_ %~ length
fromList [ Foo {fooId = 1, fooBar = 3, fooBaz = 1.0}
         , Foo {fooId = 2, fooBar = 3, fooBaz = 2.0}
         , Foo {fooId = 3, fooBar = 5, fooBaz = 3.0}
         , Foo {fooId = 4, fooBar = 4, fooBaz = 4.0}
         , Foo {fooId = 5, fooBar = 4, fooBaz = 5.0} ]
```

If you edit multiple fields, the edits all take place at the same time. so we can offset or swap a bunch of keys:

```haskell
>>> test & with FooId (>=) 2.rows.fooId_ +~ 1
fromList [ Foo {fooId = 1, fooBar = "One", fooBaz = 1.0}
         , Foo {fooId = 3, fooBar = "Two", fooBaz = 2.0}
         , Foo {fooId = 4, fooBar = "Three", fooBaz = 3.0}
         , Foo {fooId = 5, fooBar = "Four", fooBaz = 4.0}
         , Foo {fooId = 6, fooBar = "Five", fooBaz = 5.0} ]
```

We can do grouping by arbitrary functions or fields similarly

```haskell
>>> test ^@.. group (length.fooBar)
[ (3, fromList [ Foo {fooId = 1, fooBar = "One", fooBaz = 1.0}
               , Foo {fooId = 2, fooBar = "Two", fooBaz = 2.0} ])
, (4, fromList [ Foo {fooId = 4, fooBar = "Four", fooBaz = 4.0}
               , Foo {fooId = 5, fooBar = "Five", fooBaz = 5.0} ])
, (5, fromList [Foo {fooId = 3, fooBar = "Three", fooBaz = 3.0} ])
]
```

Contact Information
-------------------

Contributions and bug reports are welcome!

Please feel free to contact me through github or on the #haskell or #haskell-lens IRC channels on irc.freenode.net.

-Edward Kmett
