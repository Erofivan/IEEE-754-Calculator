#if __cplusplus > 202600L
    #error "std::double_sized_uint_t and std::double_sized_int_t are deprecated in C++23 and later."
#endif

#include <iostream>
#include <iomanip>
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <charconv>
#include <system_error>
#include <stdexcept>
#include <string>
#include <format>

namespace BigInt {

void BigInt(uint64_t r[2], uint64_t value) 
{
    r[0] = value; 
    r[1] = 0;      
}

bool GetBit(const uint64_t a[2], int i)
{
    if (i < 64) {
        return ( (a[0] >> i) & 1ULL ) != 0;
    } else {
        return ( (a[1] >> (i - 64)) & 1ULL ) != 0;
    }
}

void SetBit(uint64_t r[2], int i)
{
    if (i < 64) {
        r[0] |= (1ULL << i);
    } else {
        r[1] |= (1ULL << (i - 64));
    }
}

void ShiflLeft(uint64_t r[2], unsigned shift)
{
    if (shift == 0) {
        return;
    }
    if (shift >= 64) {
        r[1] = r[0] << (shift - 64);
        r[0] = 0;
    } else {
        uint64_t newHi = (r[1] << shift) | (r[0] >> (64 - shift));
        uint64_t newLo = (r[0] << shift);
        r[1] = newHi;
        r[0] = newLo;
    }
}

void DivByUInt64(const uint64_t a[2], uint64_t divisor, uint64_t q[2])
{
    q[0] = 0;
    q[1] = 0;

    uint64_t remainder = 0;

    for (int i = 127; i >= 0; i--) {
        remainder = (remainder << 1) | (GetBit(a, i) ? 1ULL : 0ULL);
        if (remainder >= divisor) {
            remainder -= divisor;
            SetBit(q, i);
        }
    }
}

struct Precision{
    bool is_less_than_half = false;
    bool is_equal_to_half = false;
    bool is_greater_than_half = false;
    bool is_zero = false;

    Precision(bool a, bool b, bool c, bool d) 
    :
        is_less_than_half(a),
        is_equal_to_half(b),
        is_greater_than_half(c),
        is_zero(d)
    {}
};

Precision WasPrecisionLost(const uint64_t a[2], int shift) {
    bool is_less_than_half = false;
    bool is_equal_to_half = false;
    bool is_greater_than_half = false; 
    bool is_zero = false; 

    if (GetBit(a, shift-1)) {
        is_equal_to_half = true;
        is_zero = false;
    } else {
        is_equal_to_half = false;
        is_zero = true;
    }
    for (int i = shift - 2; i > -1; --i) {
        if (GetBit(a, i) && is_equal_to_half) {
            is_greater_than_half = true;
            is_equal_to_half = false;
            return Precision(is_less_than_half, is_equal_to_half, is_greater_than_half, is_zero);
        } else if (GetBit(a, i) && is_zero) {
            is_less_than_half = true;
            is_zero = false;
            return Precision(is_less_than_half, is_equal_to_half, is_greater_than_half, is_zero);
        } 
    }
    return Precision(is_less_than_half, is_equal_to_half, is_greater_than_half, is_zero);
}

template <typename T>
Precision ShiftLeftAndDivide(T a, T b, unsigned shift, int shift_fix_factor) {
    uint64_t bigA[2];
    BigInt(bigA, static_cast<uint64_t>(a));

    shift += 64;
    ShiflLeft(bigA, shift);

    uint64_t q[2];
    DivByUInt64(bigA, static_cast<uint64_t>(b), q);

    return WasPrecisionLost(q, shift_fix_factor + 64);
} 

} // namespace BigInt

namespace std {
    template <typename T>
    struct double_sized_uint;

    template <>
    struct double_sized_uint<uint16_t> {
        using type = uint32_t;
    };

    template <>
    struct double_sized_uint<uint32_t> { 
        using type = uint64_t; 
    };

    template <typename T>
    using double_sized_uint_t = typename double_sized_uint<T>::type;

    template <typename T>
    struct double_sized_int;

    template <>
    struct double_sized_int<int16_t> {
        using type = int32_t;
    };

    template <>
    struct double_sized_int<int32_t> { 
        using type = int64_t; 
    };

    template <typename T>
    using double_sized_int_t = typename double_sized_int<T>::type;
}

namespace floating_point {

enum class RoundingType{
    kTowardZero,
    kTowardNearestEven,
    kTowardPosInfinity,
    kTowardNegInfinity
};

std::ostream& operator<<(std::ostream& os, RoundingType rounding_type) {
    os << static_cast<size_t>(rounding_type);
    return os;
}

template <typename T>
class FloatingPoint {
public:
    using uintT_t = T; 
    using intT_t  = std::make_signed_t<uintT_t>; 
    using uint2T_t = std::double_sized_uint_t<uintT_t>;
    using int2T_t = std::double_sized_int_t<intT_t>;
private:
    T value_;
    RoundingType rounding_type_;
    T exponent_bits_cnt_; 
    T total_bits_cnt_;
public:

    // This constructor creates a FloatingPoint number from a decimal number
    // @example 
    // If you have a HalfPrecision number that looks like that in the binary form:
    // 1_01010_111011101
    // Then all you need to do is to convert this number into decimal and give it
    // to this constructor
    FloatingPoint(T value = 0, RoundingType rounding_type = RoundingType::kTowardZero) 
    :    
        value_(value),
        rounding_type_(rounding_type)
    {
        if (std::is_same_v<T, uint16_t>) {
            total_bits_cnt_    = 16;
            exponent_bits_cnt_ = 5; 
        } else if (std::is_same_v<T, uint32_t>) {
            total_bits_cnt_    = 32;
            exponent_bits_cnt_ = 8;
        }
    }

    FloatingPoint(T sign_bit, T exponent, T mantissa, RoundingType rounding_type = RoundingType::kTowardZero) 
    :
        rounding_type_(rounding_type)
    {
        if (std::is_same_v<T, uint16_t>) {
            total_bits_cnt_    = 16;
            exponent_bits_cnt_ = 5; 
        } else if (std::is_same_v<T, uint32_t>) {
            total_bits_cnt_    = 32;
            exponent_bits_cnt_ = 8;
        }
        mantissa %= (1ull << (total_bits_cnt_ - exponent_bits_cnt_ - 1));
        value_ = sign_bit << (total_bits_cnt_ - 1);
        value_ += (exponent << (total_bits_cnt_ - exponent_bits_cnt_ - 1));
        value_ += mantissa;
    }

    /**
     * @warning
     * This constructor is specifically designed for operator+
     */
    FloatingPoint(int2T_t value, 
                  intT_t exponent_res, 
                  bool sign, 
                  RoundingType rounding_type, 
                  int2T_t last_remainder, 
                  int2T_t divisor)
    : 
        rounding_type_(rounding_type)
    {
        intT_t inf_plus = 0;
        if (std::is_same_v<T, uint16_t>) {
            total_bits_cnt_    = 16;
            exponent_bits_cnt_ = 5; 
            inf_plus = 31744;
        } else if (std::is_same_v<T, uint32_t>) {
            total_bits_cnt_    = 32;
            exponent_bits_cnt_ = 8;
            inf_plus = 2139095040;
        }
        
        value_ = sign ? (1ull << (total_bits_cnt_ - 1)) : 0;
    
        if (value == 0 && !last_remainder) {
            return;
        }
    
    
        intT_t shift = 0;
        uint2T_t mantissa = static_cast<uint2T_t>(std::abs(value));
        last_remainder = std::abs(last_remainder);
        divisor = std::abs(divisor);
        
        if (mantissa >> GetMantissaBitsCnt()) {
            while (mantissa >> (GetMantissaBitsCnt() + 1)) {
                ++shift;
                last_remainder += (mantissa & 1) * divisor;
                divisor <<= 1;
                mantissa >>= 1;
            }
        } else {
            while (!(mantissa >> GetMantissaBitsCnt()) && exponent_res + shift > GetMinExponent()) {
                mantissa <<= 1;
                last_remainder <<= 1;
                mantissa += last_remainder / divisor;
                last_remainder %= divisor;
                --shift;
            }
        }
        
        if (!(mantissa >> GetMantissaBitsCnt())) {
            --shift;
        }
        mantissa &= (uint2T_t(1) << GetMantissaBitsCnt()) - 1;
        
        int2T_t resulting_sign = sign ? -1 : 1;
        int2T_t signed_mantissa;
    
        
        signed_mantissa = resulting_sign * mantissa;

        int fix_cnt;
        divisor >>= 1;
        switch (rounding_type) {
            case RoundingType::kTowardZero: {
                fix_cnt = 0;
                break;
            }
            case RoundingType::kTowardNearestEven: {
                if (last_remainder == divisor && divisor == 0) {
                    fix_cnt = 0;
                    break;
                }
                if (last_remainder > divisor) {
                    fix_cnt = 1;
                } else if (last_remainder == divisor) {
                    if (mantissa & 1) {
                        fix_cnt = 1;
                    } else {
                        fix_cnt = 0;
                    }
                } else {
                    fix_cnt = 0;
                }
                break;
            }
            case RoundingType::kTowardPosInfinity: {
                if (IsNegative()) {
                    fix_cnt = 0;
                } else {
                    if (last_remainder) {
                        fix_cnt = 1;
                    }   else {
                        fix_cnt = 0;
                    }
                }
                break;
            }
            case RoundingType::kTowardNegInfinity: {
                if (IsNegative()) {
                    if (last_remainder) {
                        fix_cnt = 1;
                    } else {
                        fix_cnt = 0;
                    }
                } else {
                    fix_cnt = 0;
                }
                break;
            }
        }


        mantissa = static_cast<uintT_t>(std::abs(signed_mantissa)) + fix_cnt;
        
        if (mantissa >> GetMantissaBitsCnt()) {
            ++shift;
            mantissa &= (uint2T_t(1) << GetMantissaBitsCnt()) - 1;
        }
        
        if (exponent_res + shift >= static_cast<intT_t>(GetMaxExponentValue() - GetBias())) {
            if (    rounding_type == RoundingType::kTowardZero  
                || (rounding_type == RoundingType::kTowardPosInfinity &&  sign) 
                || (rounding_type == RoundingType::kTowardNegInfinity && !sign) ) {
                value_ += inf_plus - 1;
                return;
            } else {
                value_ += inf_plus;
                return;
            }
        }
    
        value_ += mantissa;
        value_ += (exponent_res + shift + GetMaxExponentValue() - GetBias() - 1) << GetMantissaBitsCnt();
    }

    bool IsHalfPrecision() const noexcept {
        return GetExponentBitsCnt() == 5;
    }

    bool IsSinglePrecision() const noexcept {
        return GetExponentBitsCnt() == 8;
    }

    void SetValue(uintT_t value) {
        value_ = value;
    }

    uintT_t GetValue() const noexcept {
        return value_;
    }

    RoundingType GetRoudingType() const noexcept{
        return rounding_type_;
    }

    uintT_t GetTotalBitsCnt() const noexcept{
        return total_bits_cnt_;
    }

    uintT_t GetSignBit() const noexcept {
        return (value_ >> (GetTotalBitsCnt() - 1)) & 1;
    }

    bool IsNegative() const noexcept {
        return GetSignBit();
    }

    uintT_t GetExponentBitsCnt() const noexcept {
        return exponent_bits_cnt_;
    }

    uintT_t GetExponentValue() const noexcept {
        uintT_t temp = value_;
        temp <<= 1;
        temp >>= 1;
        temp >>= GetMantissaBitsCnt();
        return temp;
    }
    
    uintT_t GetMaxExponentValue() const noexcept {
        return (1 << GetExponentBitsCnt()) - 1;
    }

    intT_t GetMinExponent() const noexcept {
        return 1 - GetBias();
    }

    intT_t GetExponent() const noexcept {
        // The exponent is either ExponentValue - Bias or MinExponent
        intT_t temp = GetExponentValue() - GetBias();
        if (GetMinExponent() > temp) { 
            return GetMinExponent();
        } else {
            return temp;
        }
    }
    
    uintT_t GetMantissaBitsCnt() const noexcept {
        return GetTotalBitsCnt() - GetExponentBitsCnt() - 1;
    }

    uintT_t GetMantissaValue() const noexcept {
        uintT_t temp = value_;
        temp <<= (GetExponentBitsCnt() + 1);
        temp >>= (GetExponentBitsCnt() + 1);
        return temp;
    }

    uintT_t GetPrecision() const noexcept {
        return GetTotalBitsCnt() - GetExponentBitsCnt();
    }

    uintT_t GetBias() const noexcept {
        return (1 << (GetExponentBitsCnt() - 1)) - 1;
    }

    void SetRoundingType(RoundingType rounding_type) {
        rounding_type_ = rounding_type;
    }

    bool IsNan() const noexcept {
        return GetExponentValue() == GetMaxExponentValue() && GetMantissaValue() != 0;
    }

    bool IsQuietNan() const noexcept {
        uintT_t first_bit_of_mantissa = value_;
        first_bit_of_mantissa <<= (GetExponentBitsCnt() + 1);
        first_bit_of_mantissa >>= (GetExponentBitsCnt() + 1);
        first_bit_of_mantissa >>= (GetMantissaBitsCnt() - 1);
        return IsNan() && (first_bit_of_mantissa & 1);
    }

    bool IsSignalingNan() const noexcept {
        return IsNan() && !IsQuietNan();
    }

    bool IsInfinite() const noexcept {
        return GetExponentValue() == GetMaxExponentValue() && GetMantissaValue() == 0;
    }

    bool IsPosInfinity() const noexcept {
        return IsInfinite() && !GetSignBit();
    }

    bool IsNegInfinity() const noexcept {
        return IsInfinite() && GetSignBit();
    }

    bool IsNormal() const noexcept {
        return 1 <= GetExponentValue() && GetExponentValue() <= GetMaxExponentValue() - 1;
    }

    bool IsSubnormal() const noexcept {
        return GetExponentValue() == 0 && GetMantissaValue() != 0;
    }

    bool IsZero() const noexcept {
        return GetExponentValue() == 0 && GetMantissaValue() == 0;
    } 
    
    bool IsPosZero() const noexcept {
        return IsZero() && !GetSignBit();
    }

    bool IsNegZero() const noexcept {
        return IsZero() && GetSignBit();
    }

    // probablye should have moved it to separate function, instead f leavian it in class
    std::string GetMantissaHexValue() {
        uintT_t temp = GetMantissaValue();
        if (IsHalfPrecision()) {
            temp <<= 2;
            std::string s = std::format("{:#05x}", temp);
            return s.substr(2, s.size());
        } else {
            temp <<= 1;
            std::string s = std::format("{:#08x}", temp);
            return s.substr(2, s.size());
        }
    }

    // probably should have moved it to a separate function, instead of leavian it in class
    std::string GetHexString() {
        if (IsHalfPrecision()) {
            std::string s = std::format("{:#06X}", GetValue());
            s[1] += 32;
            return s;
        } else {
            std::string s = std::format("{:#010X}", GetValue());
            s[1] += 32;
            return s;
        }
    }
};

//returns nth bits of the number starting from the smallest
template <typename T>
bool GetBit(T value, size_t bit_position) {
    return value & (1ull << bit_position);
}

//should move it to the class to make nan supported for all types
template <typename T>
FloatingPoint<T> Nan() {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(65024, RoundingType::kTowardZero);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(4290772992, RoundingType::kTowardZero);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> PosInfinity(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(31744, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(2139095040, rounding_type);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> NegInfinity(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(64512, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(4286578688, rounding_type);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> PosZero(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(0, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(0, rounding_type);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> NegZero(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(32768, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(2147483648, rounding_type);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> LargestPosNum(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(31743, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(2139095039, rounding_type);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> SmallestPosNumber(RoundingType rounding_type = RoundingType::kTowardZero) {
    return FloatingPoint<T>(1, rounding_type);
}

template <typename T>
FloatingPoint<T> SmallestNegNum(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>) {
        return FloatingPoint<T>(64511, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(4286578687, rounding_type);
    }
    return FloatingPoint<T>();
}

template <typename T>
FloatingPoint<T> LargestNegNumber(RoundingType rounding_type = RoundingType::kTowardZero) {
    if (std::is_same_v<T, uint16_t>)  {
        return FloatingPoint<T>(32769, rounding_type);
    } else if (std::is_same_v<T, uint32_t>) {
        return FloatingPoint<T>(2147483649, rounding_type);
    }
    return FloatingPoint<T>();
}

// Mutes signaling nan's; does not change already queit nan's
template <typename T>
FloatingPoint<T> MuteNan(FloatingPoint<T> nan) {
    if (std::is_same_v<T, uint16_t>)  {
        int64_t value = nan.GetValue();
        value += (!GetBit(value, nan.GetMantissaBitsCnt() - 1)) * (1ull << (nan.GetMantissaBitsCnt() - 1));
        return FloatingPoint<T>(value);
    } else if (std::is_same_v<T, uint32_t>) {
        int64_t value = nan.GetValue();
        value += (!GetBit(value, nan.GetMantissaBitsCnt() - 1)) * (1ull << (nan.GetMantissaBitsCnt() - 1));
        return FloatingPoint<T>(value);
    }
}

template <typename T>
FloatingPoint<T> Negate(FloatingPoint<T> num) {
    return FloatingPoint<T>(!num.GetSignBit(), num.GetExponentValue(), num.GetMantissaValue(), num.GetRoudingType());
}

template <typename T>
bool operator==(FloatingPoint<T> lhs, FloatingPoint<T> rhs) {
    return lhs.GetValue() == rhs.GetValue();
}

// Finished
template <typename T>
FloatingPoint<T> operator+(FloatingPoint<T> lhs, FloatingPoint<T> rhs) {
    using intT_t = typename FloatingPoint<T>::intT_t;
    using uintT_t = typename FloatingPoint<T>::uintT_t;
    using int2T_t = std::double_sized_int_t<intT_t>;
    using uint2T_t = std::double_sized_uint_t<uintT_t>;

    // Step 1: Handle special cases
    if (lhs.IsNan()) {
        return MuteNan(lhs);
    } else if (rhs.IsNan()) {
        return MuteNan(rhs);
    } else if (lhs.IsPosInfinity() && rhs.IsPosInfinity()) {
        return PosInfinity<T>();
    } else if (lhs.IsPosInfinity() && rhs.IsNegInfinity() || lhs.IsNegInfinity() && rhs.IsPosInfinity()) {
        return Nan<T>();
    } else if (lhs.IsNegInfinity() && rhs.IsNegInfinity()) {
        return NegInfinity<T>();
    } else if (lhs.IsPosZero() && rhs.IsPosZero()) {
        return PosZero<T>();
    } else if (lhs.IsPosZero() && rhs.IsNegZero() || lhs.IsNegZero() && rhs.IsPosZero()) {
        if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
            return NegZero<T>();
        } else {
            return PosZero<T>();
        }
    } else if (lhs.IsNegZero() && rhs.IsNegZero()) {
        return NegZero<T>();
    } else if (lhs.IsZero()) {
        return rhs;
    } else if (rhs.IsZero()) {
        return lhs;
    } else if (lhs.IsInfinite()) {
        return lhs;
    } else if (rhs.IsInfinite()) {
        return rhs;
    }

    // Step 1.5
    if (lhs == Negate<T>(rhs)) {
        if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
            return NegZero<T>();
        } else {
            return PosZero<T>();
        }
    }
     
    bool is_positive = (rhs.IsNegative() == lhs.IsNegative());
    
    intT_t exp1 = std::max<intT_t>(static_cast<intT_t>(lhs.GetMinExponent()), lhs.GetExponent());
    intT_t exp2 = std::max<intT_t>(static_cast<intT_t>(lhs.GetMinExponent()), rhs.GetExponent());
    uintT_t exp_diff = std::abs(exp1 - exp2);
    
    int2T_t result;
    int2T_t ost = 0;
    int2T_t ost_l = 0;

    int2T_t divisor = 1ull << std::min<uintT_t>(exp_diff, static_cast<uintT_t>(lhs.GetMantissaBitsCnt() + 3));
    

    long long temp1 = lhs.GetMantissaValue() + (lhs.IsNormal() << lhs.GetMantissaBitsCnt());
    temp1 *= (lhs.IsNegative() ? -1 : 1);
    long long temp2 = rhs.GetMantissaValue() + (rhs.IsNormal() << rhs.GetMantissaBitsCnt());
    temp2 *= (rhs.IsNegative() ? -1 : 1);

    if (exp2 < exp1) {
        ost_l = (std::abs(temp2) & (divisor - 1)) * (is_positive ? 1 : -1);
        ost = (divisor + ost_l) & (divisor - 1);
        result = temp1 + ((lhs.IsNegative() ? 1 : -1) * (!is_positive && ost)) + temp2 / divisor;
    } else if (exp1 < exp2) {
        ost_l = (std::abs(temp1) & (divisor - 1)) * (is_positive ? 1 : -1);
        ost = (divisor + ost_l) & (divisor - 1);
        result = temp2 + ((rhs.IsNegative() ? 1 : -1) * (!is_positive && ost)) + temp1 / divisor;
        exp1 = exp2;
    } else {
        result = temp1 + temp2;
    }

    bool sign = result < 0;
    if (!result && !ost) {
        if (lhs.IsNegative() && rhs.IsNegative()) {
            sign = true;
        } else if (lhs.IsNegative() != rhs.IsNegative()) {
            sign = false;
        } else if (!lhs.IsNegative() && !rhs.IsNegative()) {
            sign = false;
        }
    }
    
    return FloatingPoint<T>(result, exp1, sign, lhs.GetRoudingType(), ost, divisor);
}

// Finished
template <typename T>
FloatingPoint<T> operator-(FloatingPoint<T> lhs, FloatingPoint<T> rhs) {
    if (lhs.IsNan()) {
        return MuteNan<T>(lhs);
    }
    if (rhs.IsNan()) {
        return MuteNan<T>(rhs);
    }

    return lhs + Negate(rhs);
}

// Finished
template <typename T>
FloatingPoint<T> operator/(FloatingPoint<T> lhs, FloatingPoint<T> rhs) {
    // FloatingPoint specisialization dependant types    
    using intT_t = typename FloatingPoint<T>::intT_t;
    using uintT_t = typename FloatingPoint<T>::uintT_t;
    using int2T_t = std::double_sized_int_t<intT_t>;
    using uint2T_t = std::double_sized_uint_t<uintT_t>;

    // Step 1: handle special cases
    if (lhs.IsNan() && rhs.IsNan()) {
        return MuteNan<T>(lhs); 
    } else if (lhs.IsNan()) {
        return MuteNan<T>(lhs);
    } else if (rhs.IsNan()) {
        return MuteNan<T>(rhs);
    } else if (lhs.IsZero() && rhs.IsZero() || lhs.IsInfinite() && rhs.IsInfinite()) {
        return Nan<T>();
    } else if (lhs.IsInfinite() && rhs.IsZero()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosInfinity<T>() : NegInfinity<T>());
    } else if (lhs.IsZero() && rhs.IsInfinite()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosZero<T>() : NegZero<T>());
    } else if (rhs.IsZero()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosInfinity<T>() : NegInfinity<T>());
    } else if (lhs.IsZero()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosZero<T>() : NegZero<T>());
    } else if (rhs.IsInfinite()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosZero<T>() : NegZero<T>());
    } else if (lhs.IsInfinite()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosInfinity<T>() : NegInfinity<T>());
    }

    // Step 2: Find out result sign bit
    bool is_negative = (lhs.GetSignBit() != rhs.GetSignBit() ? true : false);

    // Step 3: Get the significand of both numbers in format 1.M or 0.M, where M is a bit string of mantissa (Ex.: 1.0011011001)
    uint2T_t temp1 = lhs.GetMantissaValue() + (lhs.IsNormal() << lhs.GetMantissaBitsCnt());
    uint2T_t temp2 = rhs.GetMantissaValue() + (rhs.IsNormal() << rhs.GetMantissaBitsCnt());

    // Step 3.5:  Get rid of extra zeros in temp2
    int fix_cnt = 0;
    while (!(temp2 & 1)) {
        temp2 >>= 1;
        fix_cnt++;
    }

    // Step 4: multiply significands
    uintT_t temp_shift = 2 * lhs.GetTotalBitsCnt() - (lhs.GetMantissaBitsCnt() + 1);
    uint2T_t value = (temp1 << temp_shift) / temp2;

    // Step 5: get the result exponent
    intT_t exponent_fix_factor;
    if (lhs.IsHalfPrecision()) {
        exponent_fix_factor = 0;
    } else if (lhs.IsSinglePrecision()) {
        exponent_fix_factor = 7;
    }

    intT_t exponent = lhs.GetExponent() - rhs.GetExponent() - fix_cnt + exponent_fix_factor;

    // Step 6: normalize the number
    int shift_factor = lhs.GetMantissaBitsCnt() + 1;
    intT_t temp_shift_fix_factor = shift_factor;


    int2T_t ref1 = (1ull << (2 * lhs.GetMantissaBitsCnt() + 2)) - 1;
    while (value > ref1) {
        ref1 <<= 1ull;
        ++exponent;
        ++shift_factor;
        ++temp_shift_fix_factor;
    }
    int2T_t ref2 = 1ull << (2 * lhs.GetMantissaBitsCnt() + 1);
    while (value < ref2 && value) {
        ref2 >>= 1ull;
        --exponent;
        --shift_factor;
        --temp_shift_fix_factor;
    }
    for (int i = exponent; i < lhs.GetMinExponent(); ++i) {
        ++shift_factor;
        ++temp_shift_fix_factor;
    }

    // Step 6.5: Get extra rouding precision
    BigInt::Precision remainder_flags = BigInt::ShiftLeftAndDivide(temp1, temp2, temp_shift, temp_shift_fix_factor);
    auto [is_less_than_half, is_equal_to_half, is_greater_than_half, is_zero] = remainder_flags;

    // Step 7: round the result
    switch (lhs.GetRoudingType()) {
        case RoundingType::kTowardZero: {
            value >>= shift_factor;
            break;
        }
        case RoundingType::kTowardNearestEven: {
            // int2T_t remainder = value % (1ull << shift_factor);

            value >>= shift_factor;

            if (is_greater_than_half) {
                value += 1;
                if (value == 1024 && !is_zero) {
                    ++exponent;
                }
                if ((!is_zero) && value == 1) {
                    exponent++;
                }
            } else if (is_less_than_half) {
                break;
            } else if (is_zero) {
                break;
            } else {
                if ( (value & 1) && (!is_negative) ) {
                    value += 1;
                    if (value == 1024 && !is_zero) {
                        ++exponent;
                    }
                } else if ( !(value & 1) && (!is_negative) ) {

                } else if ( (value & 1) && is_negative ) {
                    value += 1;
                    if (value == 1024 && !is_zero) {
                        ++exponent;
                    }
                } else if ( !(value & 1) && is_negative ) {
                    
                }
                if ((!is_zero) && value == 1) {
                    exponent++;
                }
            }
            
            break;
        }
        case RoundingType::kTowardPosInfinity: {
            intT_t remainder = (!is_zero);

            value >>= shift_factor;

            if (!is_negative) {
                value += remainder;
                if (value == 1024 && !is_zero) {
                    ++exponent;
                }
                if (remainder && value == 1) {
                    exponent++;
                }
            }
            break;
        }
        case RoundingType::kTowardNegInfinity: {
            intT_t remainder = (!is_zero);

            value >>= shift_factor;

            if (is_negative) {
                value += remainder;
                if (value == 1024 && !is_zero) {
                    ++exponent;
                }
                if (remainder && value == 1) {
                    exponent++;
                }
            }
            break;
        }
    }

    // Handle cases then we need to round all possible bits
    if (shift_factor == lhs.GetMaxExponentValue() + 1 && exponent == lhs.GetMinExponent() - static_cast<intT_t>(lhs.GetMantissaBitsCnt()) - 1) {
        if (is_greater_than_half) {
            if (lhs.GetRoudingType() == RoundingType::kTowardNearestEven) {
                return (is_negative ? LargestNegNumber<T>() : SmallestPosNumber<T>());
            } else if (lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return (is_negative ? NegZero<T>() : SmallestPosNumber<T>());
            } else if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return (is_negative ? LargestNegNumber<T>() : PosZero<T>());
            }
        } else if (!is_zero) {
            if (lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return (is_negative ? NegZero<T>() : SmallestPosNumber<T>());
            } else if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return (is_negative ? LargestNegNumber<T>() : PosZero<T>());
            }
        }
    }

    // Step 8: handle overflow and undeflow
    if (exponent >= static_cast<intT_t>(lhs.GetMaxExponentValue() - lhs.GetBias())) {
        if (!is_negative) {
            if (lhs.GetRoudingType() == RoundingType::kTowardNearestEven || lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return PosInfinity<T>();
            } else {
                return LargestPosNum<T>();
            }
        } else {
            if (lhs.GetRoudingType() == RoundingType::kTowardNearestEven || lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return NegInfinity<T>();
            } else {
                return SmallestNegNum<T>();
            } 
        }
    } else if (exponent < static_cast<intT_t>(lhs.GetMinExponent() - lhs.GetMantissaBitsCnt())) {
        if (!is_negative) {
            if (lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return SmallestPosNumber<T>();
            } else {
                return PosZero<T>();
            }
        } else {
            if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return LargestNegNumber<T>();
            } else {
                return NegZero<T>();
            }
        }
    }

    if (exponent + static_cast<intT_t>(lhs.GetBias()) > 0) {
        return FloatingPoint<T>(is_negative, exponent + lhs.GetBias(), value);
    } else {
        return FloatingPoint<T>(is_negative, 0, value);
    }

}

// Finished
template <typename T>
FloatingPoint<T> operator*(FloatingPoint<T> lhs, FloatingPoint<T> rhs) {
    // FloatingPoint specisialization dependant types    
    using intT_t = typename FloatingPoint<T>::intT_t;
    using uintT_t = typename FloatingPoint<T>::uintT_t;
    using int2T_t = std::double_sized_int_t<intT_t>;
    using uint2T_t = std::double_sized_uint_t<uintT_t>;

    // Step 1: handle special cases
    if (lhs.IsNan() && rhs.IsNan()) {
        return MuteNan<T>(lhs);
    } else if (lhs.IsNan()) {
        return MuteNan<T>(lhs);
    } else if (rhs.IsNan()) {
        return MuteNan<T>(rhs);
    } else if (lhs.IsZero() && rhs.IsInfinite() || lhs.IsInfinite() && rhs.IsZero()) {
        return Nan<T>();
    } else if (lhs.IsInfinite() || rhs.IsInfinite()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosInfinity<T>(lhs.GetRoudingType()) : NegInfinity<T>(lhs.GetRoudingType()));
    } else if (lhs.IsZero() || rhs.IsZero()) {
        return (lhs.GetSignBit() == rhs.GetSignBit() ? PosZero<T>(lhs.GetRoudingType()) : NegZero<T>(lhs.GetRoudingType()));
    } else if (lhs.IsSubnormal() && rhs.IsSubnormal()) {
        if (lhs.GetSignBit() == rhs.GetSignBit()) {
            if (lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return SmallestPosNumber<T>(lhs.GetRoudingType());
            } else {
                return PosZero<T>(lhs.GetRoudingType());
            }
        } else {
            if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return LargestNegNumber<T>(lhs.GetRoudingType());
            } else {
                return NegZero<T>(lhs.GetRoudingType());
            }
        }
    }

    // Step 2: find out result sign bit
    bool is_negative = (lhs.GetSignBit() != rhs.GetSignBit() ? true : false);

    // Step 3: Get the significand of both numbers in format 1.M or 0.M, where M is a bit string of mantissa (Ex.: 1.0011011001)
    uint2T_t temp1 = lhs.GetMantissaValue() + (lhs.IsNormal() << lhs.GetMantissaBitsCnt());
    uint2T_t temp2 = rhs.GetMantissaValue() + (rhs.IsNormal() << rhs.GetMantissaBitsCnt());

    // Step 4: multiply significands
    uint2T_t value = temp1 * temp2;

    // Step 5: get the result exponent
    intT_t exponent = lhs.GetExponent() + rhs.GetExponent();

    // Step 6: normalize the number
    int shift_factor = lhs.GetMantissaBitsCnt();

    int2T_t ref1 = (1ull << (2 * lhs.GetMantissaBitsCnt() + 1)) - 1;
    while (value > ref1) {
        ref1 <<= 1;
        ++shift_factor;
        ++exponent;
    }
    int2T_t ref2 = 1ull << (2 * lhs.GetMantissaBitsCnt());
    while (value < ref2 && value) {
        ref2 >>= 1;
        --shift_factor;
        --exponent;
    }
    for (int i = exponent; i < lhs.GetMinExponent(); ++i) {
        ++shift_factor;
    }

    // Step 7: round the result
    switch (lhs.GetRoudingType()) {
        case RoundingType::kTowardZero: {
            value >>= shift_factor;
            break;
        }
        case RoundingType::kTowardNearestEven: {
            int2T_t remainder = value % (1ull << shift_factor);

            value >>= shift_factor;

            if (remainder > (1ull << (shift_factor - 1))) {
                value += 1;
                if (value == 1024) {
                    ++exponent;
                }
                if (remainder && value == 1) {
                    exponent++;
                }
            } else if (remainder < (1ull << (shift_factor - 1))) {
                break;
            } else {
                if ( (value & 1) && (!is_negative) ) {
                    value += 1;
                    if (value == 1024) {
                        ++exponent;
                    }
                } else if ( !(value & 1) && (!is_negative) ) {
                } else if ( (value & 1) && is_negative ) {
                    value += 1;
                    if (value == 1024) {
                        ++exponent;
                    }
                } else if ( !(value & 1) && is_negative ) {
                }
                if (remainder && value == 1) {
                    exponent++;
                }
            }
            
            break;
        }
        case RoundingType::kTowardPosInfinity: {
            intT_t remainder = value % (1ull << shift_factor);
            remainder = remainder != 0;

            value >>= shift_factor;

            if (!is_negative) {
                value += remainder;
                if (value == 1024) {
                    ++exponent;
                }
                if (remainder && value == 1) {
                    exponent++;
                }
            }
            break;
        }
        case RoundingType::kTowardNegInfinity: {
            intT_t remainder = value % (1ull << shift_factor);
            remainder = remainder != 0;

            value >>= shift_factor;

            if (is_negative) {
                value += remainder;
                if (value == 1024) {
                    ++exponent;
                }
                if (remainder && value == 1) {
                    exponent++;
                }
            }
            break;
        }
    }

    intT_t ref = (1ull << (lhs.GetMantissaBitsCnt() + 1));
    while (value >= ref) {
        ref <<= 1;
        exponent += 1;
    }

    // Step 8: handle overflow and undeflow
    if (exponent >= static_cast<intT_t>(lhs.GetMaxExponentValue() - lhs.GetBias())) {
        if (!is_negative) {
            if (lhs.GetRoudingType() == RoundingType::kTowardNearestEven || lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return PosInfinity<T>(lhs.GetRoudingType());
            } else {
                return LargestPosNum<T>(lhs.GetRoudingType());
            }
        } else {
            if (lhs.GetRoudingType() == RoundingType::kTowardNearestEven || lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return NegInfinity<T>(lhs.GetRoudingType());
            } else {
                return SmallestNegNum<T>(lhs.GetRoudingType());
            } 
        }
    } else if (exponent < static_cast<intT_t>(lhs.GetMinExponent() - lhs.GetMantissaBitsCnt())) {
        if (!is_negative) {
            if (lhs.GetRoudingType() == RoundingType::kTowardPosInfinity) {
                return SmallestPosNumber<T>(lhs.GetRoudingType());
            } else {
                return PosZero<T>(lhs.GetRoudingType());
            }
        } else {
            if (lhs.GetRoudingType() == RoundingType::kTowardNegInfinity) {
                return LargestNegNumber<T>(lhs.GetRoudingType());
            } else {
                return NegZero<T>(lhs.GetRoudingType());
            }
        }
    }

    if (exponent + static_cast<intT_t>(lhs.GetBias()) > 0) {
        return FloatingPoint<T>(is_negative, exponent + lhs.GetBias(), value, lhs.GetRoudingType());
    } else {
        return FloatingPoint<T>(is_negative, 0, value, lhs.GetRoudingType());
    }
}

// Finished
template <typename T>
FloatingPoint<T> mad(FloatingPoint<T> num1, FloatingPoint<T> num2, FloatingPoint<T> num3) {
    // Handle special cases
    if (num1.IsNan()) {
        return MuteNan<T>(num1);
    }
    if (num2.IsNan()) {
        return MuteNan<T>(num2);
    }
    if (num3.IsNan()) {
        return MuteNan<T>(num3);
    }

    return num1 * num2 + num3;
}


/** @note
  * Basically this operation is a copy-paste of both * and + operators but with
  * minor changes like removing intermediate rounding and fixing some bugs
  * that occur during calculation.
  * I would recommend you to scroll through * and + operators first and 
  * understand their logic, before going here
  */
template <typename T>
FloatingPoint<T> fma(FloatingPoint<T> num1, FloatingPoint<T> num2, FloatingPoint<T> num3) {
    // Step 1: Handle special cases
    if (num1.IsNan()) {
        return MuteNan<T>(num1);
    }
    if (num2.IsNan()) {
        return MuteNan<T>(num2);
    }
    if (num3.IsNan()) {
        return MuteNan<T>(num3);
    }

    return num1 * num2 + num3;
}

template <typename T>
std::ostream& operator<<(std::ostream& os, FloatingPoint<T> fp) {
    // Special cases handling
    if (fp.IsInfinite()) {
        if (fp.IsPosInfinity()) {
            os << "inf";
        } else {
            os << "-inf";
        }
    } else if (fp.IsNan()) {
        os << "nan";
    } else if (fp.IsZero()) {
        if (fp.IsPosZero()) {
            if (fp.IsHalfPrecision()) {
                os << "0x0.000p+0";
            } else {
                os << "0x0.000000p+0";
            }
        } else {
            if (fp.IsHalfPrecision()) {
                os << "-0x0.000p+0";
            } else {
                os << "-0x0.000000p+0";
            }
        }
    } else if (fp.IsSubnormal()) {
        using uintT_t = FloatingPoint<T>::uintT_t;

        int exponent_shift_factor = 0;
        uintT_t container = fp.GetMantissaValue(); 
        while (container < (1 << fp.GetMantissaBitsCnt())) {
            container <<= 1;
            ++exponent_shift_factor;
        }
        container -= GetBit(container, fp.GetMantissaBitsCnt()) * (1 << fp.GetMantissaBitsCnt());
        FloatingPoint<T> result(fp.GetSignBit(), 0, container);

        if (result.GetSignBit()) {
            os << '-';
        }
        os << "0x1.";
        os << result.GetMantissaHexValue();
        os << 'p';
        if (result.GetExponent() >= 0) {
            os << '+';
        }
        os << std::to_string(result.GetExponent() - exponent_shift_factor);
    } else {
        if (fp.GetSignBit()) {
            os << '-';
        }
        os << "0x1.";
        os << fp.GetMantissaHexValue();
        os << 'p';
        if (fp.GetExponent() >= 0) {
            os << '+';
        }
        os << std::to_string(fp.GetExponent());
    }

    os << ' ';
    os << fp.GetHexString();
    return os;
}

template <typename T>
std::string Print3(FloatingPoint<T> fp) {
    // Special cases handling
    std::string s = "";
    if (fp.IsInfinite()) {
        if (fp.IsPosInfinity()) {
            s += "inf";
        } else {
            s += "-inf";
        }
    } else if (fp.IsNan()) {
        s += "nan";
    } else if (fp.IsZero()) {
        if (fp.IsPosZero()) {
            if (fp.IsHalfPrecision()) {
                s += "0x0.000p+0";
            } else {
                s += "0x0.000000p+0";
            }
        } else {
            if (fp.IsHalfPrecision()) {
                s += "-0x0.000p+0";
            } else {
                s +="-0x0.000000p+0";
            }
        }
    } else if (fp.IsSubnormal()) {
        using uintT_t = FloatingPoint<T>::uintT_t;

        int exponent_shift_factor = 0;
        uintT_t container = fp.GetMantissaValue(); 
        while (container < (1 << fp.GetMantissaBitsCnt())) {
            container <<= 1;
            ++exponent_shift_factor;
        }
        container -= GetBit(container, fp.GetMantissaBitsCnt()) * (1 << fp.GetMantissaBitsCnt());
        FloatingPoint<T> result(fp.GetSignBit(), 0, container);

        if (result.GetSignBit()) {
            s += "-";
        }
        s += "0x1.";
        s += result.GetMantissaHexValue();
        s += "p";
        if (result.GetExponent() >= 0) {
            s += "+";
        }
        int r = result.GetExponent() - exponent_shift_factor;
        s += std::to_string(r);
    } else {
        if (fp.GetSignBit()) {
            s.push_back('-');
        }
        s += "0x1.";
        s += fp.GetMantissaHexValue();
        s += "p";
        if (fp.GetExponent() >= 0) {
            s += "+";
        }
        int r = fp.GetExponent();
        s += std::to_string(r);
    }

    s += ' ';
    s += fp.GetHexString();
    return s;
    // return os;
}


} // namespace floating_point

using namespace floating_point;

template <typename FloatingPoint>
void Parse(int argc, char* argv[], floating_point::RoundingType rounding_type) {
    using uintT_t = typename FloatingPoint::uintT_t;
    char* arg;
    if (std::is_same_v<uintT_t, uint16_t>) {
        arg = "%hx";
    } else { 
        arg = "%x";
    }
    if (argc == 4) {
        uintT_t num;
        sscanf(argv[3], arg, &num);
        FloatingPoint fp_num(num, rounding_type);
        std::cout << fp_num;
    } else if (argc == 6) {
        char tcmd;
        sscanf(argv[3], "%c", &tcmd);
        const char cmd = tcmd;
        uintT_t tnum1 = {};
        uintT_t tnum2 = {};
        sscanf(argv[4], arg, &tnum1);
        const uintT_t num1 = tnum1;
        sscanf(argv[5], arg, &tnum2);
        const uintT_t num2 = tnum2;
        FloatingPoint fp_num1(num1, rounding_type);
        FloatingPoint fp_num2(num2, rounding_type);
        switch (cmd) {
            case '+': {
                std::cout << fp_num1 + fp_num2;
                break;
            }
            case '-': {
                std::cout << fp_num1 - fp_num2;
                break;
            }
            case '*': {
                std::cout << fp_num1 * fp_num2;
                break;
            }
            case '/': {
                std::cout << fp_num1 / fp_num2;
                break;
            }
            default: {
                break;
            }
        }
    } else {
        const char* cmd = argv[3];
        uintT_t num1;
        uintT_t num2;
        uintT_t num3;
        sscanf(argv[4], arg, &num1);
        sscanf(argv[5], arg, &num2);
        sscanf(argv[6], arg, &num3);
        FloatingPoint fp_num1(num1, rounding_type);
        FloatingPoint fp_num2(num2, rounding_type);
        FloatingPoint fp_num3(num3, rounding_type);
        if (strcmp(cmd, "mad") == 0) {
            std::cout << floating_point::mad<uintT_t>(fp_num1, fp_num2, fp_num3);
        } else if (strcmp(cmd, "fma") == 0) {
            std::cout << floating_point::fma<uintT_t>(fp_num1, fp_num2, fp_num3);
        } 
    }
}

int main(int argc, char* argv[]) {
    if (argc != 4 && argc != 6 && argc != 7) {
        std::cout << "Error: wrong amount of arguments! Expected 4, 6 or 7, but got "
                    << argc << " instead" << std::endl;
        return EXIT_FAILURE;
    }

    const char* fmt_raw_value = argv[1];
    if (strlen(fmt_raw_value) != 1 && fmt_raw_value[0] != 'h' && fmt_raw_value[0] != 's') {
        std::cout << "Error: wrong format! Expected 'h' or 's', but got "
                    << std::quoted(fmt_raw_value, '\'') << " instead" << std::endl;
        return EXIT_FAILURE;
    }
    char fp_num_format = fmt_raw_value[0];

    
    RoundingType rounding_type;
    short int temp{};
    std::from_chars_result result = std::from_chars(argv[2], argv[2]+strlen(argv[2]), temp);
    if (result.ec == std::errc() && 0 <= temp && temp <= 3 && strlen(argv[2]) == 1) { // Last check is for "-0", because from_chars ignores '-' 
        rounding_type = static_cast<RoundingType>(temp);
    } else {
        std::cout << "Error: wrong rounding type! Expected a number from 0 to 3, but got "
        << std::quoted(argv[2], '\'') << " instead" << std::endl;
        return EXIT_FAILURE;
    }   
    std::string s;
    if (fp_num_format == 'h') {
        Parse<FloatingPoint<uint16_t>>(argc, argv, rounding_type);
    } else {
        Parse<FloatingPoint<uint32_t>>(argc, argv, rounding_type);
    }
}