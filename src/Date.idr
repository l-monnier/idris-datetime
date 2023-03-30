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

%default total

||| "Lower than" proof.
||| TODO: consider moving it to its own module.
data (<) : (m,n : Integer) -> Type where
  LT : {0 m,n : Integer} -> (0 prf : (m < n) === True) -> m < n

||| Drop the fraction of the provided number.
||| For example: -1.5 becomes -1 and 1.5 becomes 1
fix : Double -> Double
fix x = if x < 0 then ceiling x else floor x

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

-- Count of days with different epochs.

||| The Julian Day (JD) is the count of days since January 1st 4713 BC (-4712).
public export
data JD = MkJD Integer

public export
Num JD where
  (MkJD x) + (MkJD y) = MkJD (x + y)
  (MkJD x) * (MkJD y) = MkJD (x * y)
  fromInteger = MkJD

||| The Rata Die number is the count of days since December 31 of the year 0.
public export
data RD = MkRD Integer

public export
Num RD where
  (MkRD x) + (MkRD y) = MkRD (x + y)
  (MkRD x) * (MkRD y) = MkRD (x * y)
  fromInteger = MkRD

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

fromMonth : Month -> Integer
fromMonth Jan = 1
fromMonth Feb = 2
fromMonth Mar = 3
fromMonth Apr = 4
fromMonth May = 5
fromMonth Jun = 6
fromMonth Jul = 7
fromMonth Aug = 8
fromMonth Sep = 9
fromMonth Oct = 10
fromMonth Nov = 11
fromMonth Dec = 12

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

||| True if the year is above is a leap year.
|||
||| Year 0 is a considered as a leap year.
||| Negative years follow the same rules as positive year.
||| For example, -4 is a leap year, but not -100.
isLeap : (year : Integer) -> Bool
isLeap year =
  let
    nthYear : Integer -> Bool
    nthYear n = mod year n == 0
  in
    (nthYear 4) && (not (nthYear 100) || (nthYear 400))

||| Number of days in the given month and year.
daysInMonth : (year : Integer) -> Month -> Integer
daysInMonth _ Jan = 31
daysInMonth year Feb = if isLeap year then 29 else 28
daysInMonth _ Mar = 31
daysInMonth _ Apr = 30
daysInMonth _ May = 31
daysInMonth _ Jun = 30
daysInMonth _ Jul = 31
daysInMonth _ Aug = 31
daysInMonth _ Sep = 30
daysInMonth _ Oct = 31
daysInMonth _ Nov = 30
daysInMonth _ Dec = 31

||| A Gregorian calendar date
export
data Date : Type where
  MkDate : (year  : Integer) -> (month : Month) -> (day   : Integer) -> Date

public export
mkDate
  :  (year : Integer)
  -> (month : Month)
  -> (day : Integer)
  -> Either DateTimeException Date
mkDate year month day with (day > 0, (daysInMonth year month) + 1 > day)
  mkDate year month day | (True , True ) = Right (MkDate year month day)
  mkDate _    _     day | (False, _    ) = Left (DayLowerThanOne day)
  mkDate year month day | (_    , False) = Left (DateDoesNotExist year month day)

||| Return a (Gregorian) calendar `Date`.
||| The arguments are statically validated.
||| e.g. 2023 Jan 0, 2023 Feb 29, 2012 Aug 35 are not allowed.
public export
mkDate'
    :  (year  : Integer)
    -> (month : Month)
    -> (day   : Integer)
    -> {auto 0 isAboveZeroDay   : 0 < day}
    -> {auto 0 isNotAboveMaxDay : day < (daysInMonth year month) + 1}
    -> Date
mkDate' year month day = MkDate year month day

||| Project the year from a Date.
public export
year : Date -> Integer
year (MkDate y _ _) = y

||| Project the month from a Date.
public export
month : Date -> Month
month (MkDate _ m _) = m

||| Project the day from a Date.
public export
day : Date -> Integer
day (MkDate _ _ d) = d

||| Convert a Gregorian Date to a Julian day.
|||
||| The first argument is the number of day between the arbitray point
||| and the date 1-Mar-0.
||| The second argument is the Gregorian Date to convert.
|||
||| The alorgorithm used is the one of Peter Baum in his article Date Algorithms:
||| https://www.researchgate.net/publication/316558298_Date_Algorithms
dateToJulianDay : (cst : Double) -> Date -> Integer
dateToJulianDay cst (MkDate year month day) =
      day
    + f month
    + cast (365 * z) + cast (floor (z / 4) - floor(z / 100) + floor (z / 400) + cst)
  where

    month' : Integer
    month' = fromMonth month

    -- The year with a shift of minus 14 months
    z : Double
    z = fromInteger year + fix ((fromInteger month' - 14) / 12)

    -- List of days in the year for a given month.
    -- The begining of the year being shifted to March,
    -- the 3rd value of the list is 0.
    f : Month -> Integer
    f Jan = 306
    f Feb = 337
    f Mar = 0
    f Apr = 31
    f May = 61
    f Jun = 92
    f Jul = 122
    f Aug = 153
    f Sep = 184
    f Oct = 214
    f Nov = 245
    f Dec = 275

||| Convert a Gregorian date to a Julian Day (JD) count.
public export
dateToJD : Date -> JD
dateToJD = MkJD . dateToJulianDay 1721118.5

||| Convert a Gregorian date to a Rata Die number.
|||
||| Note that from our tests, the function converts correctly dates up
||| to years as big as +/- 2,737,907,006,989.
||| Around such years, roundings will cause the algorithm to provide
||| incorrect results.
||| For example, 27379070069886 Jan 28 is incorrectly converted to
||| 10^16 - 1 while the result should be 10^16.
public export
dateToRD : Date -> RD
dateToRD = MkRD . dateToJulianDay (-306)

||| Convert a Julian Day count set at an arbitrary point in time to
||| a Gregorian Date typle (year, month, day).
|||
||| The first argument is the number of day between the arbitray point
||| and the date 1-Mar-0.
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

||| Rata Die number to Gregorian Date.
public export
rdToDate : RD -> Date
rdToDate (MkRD ord) = toDate $ julianDayToGregorian (-306) (fromInteger ord)
  where
    toDate : (Double, Double, Double) -> Date
    toDate (year, month, day) = MkDate (cast year) (toMonth month) (cast day)

rdToDate_1_is_correct : 1 = dateToRD (rdToDate 1)
rdToDate_1_is_correct = Refl

rdToDate_10_15_is_correct : 1000000000000000 = dateToRD (rdToDate $ 1000000000000000)
rdToDate_10_15_is_correct = Refl
