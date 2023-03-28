||| Concrete date/time and related types.


{-
 Inspired from Python's Lib/datetime.py.
 
 Gregorian calendar indefinitely extended into the future. Unlike the
 python from which this is derived library, this module uses natural
 numbers to represent dates: Dates before Jan 1, 1 C.E are
 unrepresentable 
 
 In addition, this library makes an effort to prevent representation
 of invalid julian dates, such as:
 
 2023 Mar 32
 2023 Feb 29
 1000 Jan 0
 2024 Nov 31
 
 I.e. the day of month *must* be between 1 and the number of days in
 that month, for that year.
-}

module Date

import Decidable.Equality

%default total

||| "Lower than" proof.
||| TODO: consider moving it to its own module.
data (<) : (m,n : Integer) -> Type where
  LT : {0 m,n : Integer} -> (0 prf : (m < n) === True) -> m < n

||| Abbreviated symbolic month
public export
data Month
  = Jan
  | Feb
  | Mar
  | Apr
  | May
  | Jun
  | Jul
  | Aug
  | Sep
  | Oct
  | Nov
  | Dec

||| Exceptions
data DateTimeException =
    DayLowerThanOne Integer
  | DateDoesNotExist Integer Month Integer
  | YearLowerThanOne Integer

||| Return the previous month for the given month
prevMonth : Month -> Month
prevMonth Jan = Dec
prevMonth Feb = Jan
prevMonth Mar = Feb
prevMonth Apr = Mar
prevMonth May = Apr
prevMonth Jun = May
prevMonth Jul = Jun
prevMonth Aug = Jul
prevMonth Sep = Aug
prevMonth Oct = Sep
prevMonth Nov = Oct
prevMonth Dec = Nov

||| Return the next month for the given month
nextMonth : Month -> Month
nextMonth Jan = Feb
nextMonth Feb = Mar
nextMonth Mar = Apr
nextMonth Apr = May
nextMonth May = Jun
nextMonth Jun = Jul
nextMonth Jul = Aug
nextMonth Aug = Sep
nextMonth Sep = Oct
nextMonth Oct = Nov
nextMonth Nov = Dec
nextMonth Dec = Jan

||| True if leap year, else False
isLeap' : (year : Integer) -> {auto 0 isValidYear : 0 < year} -> Bool
isLeap' year =
  let
    nthYear : Integer -> Bool
    nthYear n = mod year n == 0
  in
    (nthYear 4) && (not (nthYear 100) || (nthYear 400))

||| True if the year is above 0 and is a leap year, else False
isLeap'' : (year : Integer) -> Bool
isLeap'' year =
  let
    nthYear : Integer -> Bool
    nthYear n = mod year n == 0
  in
    year > 0 && (nthYear 4) && (not (nthYear 100) || (nthYear 400))

daysInMonth''
  :  (year : Integer)
  -> Month
  -> Integer
daysInMonth'' year month with (if year < 1 then 0 else year)
  daysInMonth'' _ _   | 0 = 0
  daysInMonth'' _ Jan | _ = 31
  daysInMonth'' year Feb | _ = if isLeap'' year then 29 else 28
  daysInMonth'' _ Mar | _ = 31
  daysInMonth'' _ Apr | _ = 30
  daysInMonth'' _ May | _ = 31
  daysInMonth'' _ Jun | _ = 30
  daysInMonth'' _ Jul | _ = 31
  daysInMonth'' _ Aug | _ = 31
  daysInMonth'' _ Sep | _ = 30
  daysInMonth'' _ Oct | _ = 31
  daysInMonth'' _ Nov | _ = 30
  daysInMonth'' _ Dec | _ = 31

||| Number of days in the given month and year
daysInMonth'
  :  (year : Integer)
  -> {auto 0 isValidYear : 0 < year}
  -> Month
  -> Integer
daysInMonth' year month = daysInMonth'' year month

||| Number of days before January 1st of the given year.
daysBeforeYear'
  :  (year : Integer)
  -> {auto 0 isValidYear : 0 < year}
  -> Integer
daysBeforeYear' year =
  (year - 1) * 365 + div year 4 - div year 100 + div year 400

daysBeforeYear''
  :  (year : Integer)
  -> Integer
daysBeforeYear'' year =
  (year - 1) * 365 + div year 4 - div year 100 + div year 400

||| Number of days in year preceding first day of month.
daysBeforeMonth'
  :  (year : Integer)
  -> {auto 0 isValidYear : 0 < year}
  -> Month
  -> Integer
daysBeforeMonth' year Jan   = 0
daysBeforeMonth' year month =
  daysInMonth' year prev + daysBeforeMonth' year (assert_smaller month prev)
  where
    prev : Month
    prev = prevMonth month

daysBeforeMonth''
  :  (year : Integer)
  -> Month
  -> Integer
daysBeforeMonth'' year Jan   = 0
daysBeforeMonth'' year month =
  daysInMonth'' year prev + daysBeforeMonth'' year (assert_smaller month prev)
  where
    prev : Month
    prev = prevMonth month

||| Number of days in the given year
daysInYear' : (year : Integer) -> {auto 0 isValidYear : 0 < year} -> Integer
daysInYear' year = if isLeap' year then 366 else 365

||| A (Gregorian) calendar date
export
data Date' : Type where
  MkDate
    :  (year  : Integer)
    -> (month : Month)
    -> (day   : Integer)
    -> Date'

public export
mkDate
  :  (year : Integer)
  -> (month : Month)
  -> (day : Integer)
  -> Either DateTimeException Date'
mkDate year month day with (year > 0)
  mkDate year _ _ | False = Left (YearLowerThanOne year)
  mkDate year month day | True with (day > 0)
    mkDate _ _ day | True | False = Left (DayLowerThanOne day)
    mkDate year month day | True | True with ((daysInMonth'' year month) + 1 > day)
      mkDate year month day | True | True | False = Left (DateDoesNotExist year month day)
      mkDate year month day | True | True | True  = Right (MkDate year month day)

||| Return a (Gregorian) calendar `Date`.
||| The arguments are statically validated.
||| e.g. 2023 Jan 0, 2023 Feb 29, 2012 Aug 35 are not allowed.
public export
mkDate'
    :  (year  : Integer)
    -> (month : Month)
    -> (day   : Integer)
    -> {auto 0 isValidYear      : 0 < year}
    -> {auto 0 isAboveZeroDay   : 0 < day}
    -> {auto 0 isNotAboveMaxDay : day < (daysInMonth' year month) + 1}
    -> Date'
mkDate' year month day = MkDate year month day

date2Ord : Date' -> Integer
date2Ord (MkDate year Jan day) =
  daysBeforeYear'' year + day
date2Ord (MkDate year month day) =
  daysBeforeYear'' year + daysBeforeMonth'' year month + day

||| Number of days in 400 years
DI400Y' : Integer
DI400Y' = daysBeforeYear' 401

||| Number of days in 100 years
DI100Y' : Integer
DI100Y' = daysBeforeYear' 101

||| Number of days in 4 years
DI4Y' : Integer
DI4Y' = daysBeforeYear' 5

DI4Y_is_correct : DI4Y' = (4 * 365 + 1)
DI4Y_is_correct = Refl

DI100Y_is_correct : DI100Y'  = 25 * DI4Y' - 1
DI100Y_is_correct = Refl

DIY_400Y_is_correct : DI400Y' = (4 * DI100Y' + 1)
DIY_400Y_is_correct = Refl

||| Convert a Julian Day count set at an arbitrary point in time to
||| a Gregorian Date typle (year, month, day).
|||
||| The first argument is the number of day between the arbitray point
||| and the (virtual) date 1-Mar-0.
||| The second argument is the Julian Day count to convert.
|||
||| The alorgorithm used is the one of Peter Baum in his article Date Algorithms:
||| https://www.researchgate.net/publication/316558298_Date_Algorithms
julianDayToGregorian : Double -> Double -> (Double, Double, Double)
julianDayToGregorian cst jd =
  if month > 12
  then (year + 1, month - 12, day)
  else (year, month, day)
  where

    -- Drop the fraction of the provided number.
    -- For example: -1.5 becomes -1 and 1.5 becomes 1
    fix : Double -> Double
    fix x = if x < 0 then ceiling x else floor x

    -- Gregorian ordinal adjusted to a reference point set on 1 March 0
    z : Double
    z = floor (jd - cst)

    -- The fractional part of the Gregorian ordinal
    r : Double
    r = jd - cst - z

    -- Value used in later steps
    g : Double
    g = z - 0.25

    -- Number of full centuries.
    a : Double
    a = floor (g / 36524.25)

    -- Number of days within the whole centuries
    b : Double
    b = a - floor (a / 4)

    year : Double
    year = floor ((b + g) / 365.25)

    -- Number of days in the current year
    c : Double
    c = b + z - floor (365.25 * year)

    month : Double
    month = fix ((5 * c + 456) / 153)

    day : Double
    day = c - fix ((153 * month - 457) / 5) + r

||| Gregorian ordinal to (Gregorian) `Date` considering 1-Jan-1 as day 1
public export
ord2ym
  :  (ord : Integer)
  -> {auto 0 isAbove0 : 0 < ord}
  -> Date'
ord2ym ord = toDate $ julianDayToGregorian (-306) (fromInteger ord)
   where
      toMonth : Double -> Month
      toMonth 1 = Jan
      toMonth 2 = Feb
      toMonth 3 = Mar
      toMonth 4 = Apr
      toMonth 5 = May
      toMonth 6 = Jun
      toMonth 7 = Jul
      toMonth 8 = Aug
      toMonth 9 = Sep
      toMonth 10 = Oct
      toMonth 11 = Nov
      toMonth 12 = Dec
      toMonth _ = Jan

      toDate : (Double, Double, Double) -> Date'
      toDate (year, month, day) =
        MkDate (cast year) (toMonth month) (cast day)

ord2ym_is_correct : 1 = date2Ord (ord2ym 1)
ord2ym_is_correct = Refl

test : (n : Integer) -> {auto 0 prf : 0 < n} -> {auto 0 test : n = date2Ord (ord2ym n)} -> Bool
test _ = True

{-
||| Proleptic Gregorian ordinal for the year, month and day.
|||
||| January 1 of year 1 is day 1.
public export
toOrdinal : Date -> Nat
toOrdinal (MkDate ord) = ord

||| Project the year, month, and day from a Date.
public export
toYMD : Date -> (Nat, Month, Nat)
toYMD (MkDate date) = ord2ymd date

||| Project the year from a Date.
public export
year : Date -> Nat
year date = fst (toYMD date)

||| Project the month from a Date
public export
month : Date -> Month
month date = let (_, m, _ ) := (toYMD date) in m

||| Project the day from a Date
public export
day : Date -> Month
day date = let (_, _, d) := (toYMD date) in d


-}
