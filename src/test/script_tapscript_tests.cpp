// Copyright (c) 2011-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <test/data/script_tests.json.h>
#include <test/data/bip341_wallet_vectors.json.h>

#include <script/interpreter.h>
#include <script/script.h>
#include <script/script_error.h>
#include <test/util/setup_common.h>
#include <test/util/transaction_utils.h>

#include <boost/test/unit_test.hpp>
#include <boost/test/execution_monitor.hpp>

#include <univalue.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

/*DSB*/#include <iostream>

namespace {

/**
 * For these tests don't need _real_ signature/pubkey validation.  That is
 * tested elsewhere.  So we just _mock_ the signature checker and force it
 * to answer valid/invalid as we wish.
 */

class SignatureCheckerMock : public BaseSignatureChecker
{
public:

  //! Whether this mock always validates, or always fails, the signature/pubkey check.
  enum class VALIDATION { ALWAYS_SUCCEEDS, ALWAYS_FAILS };
  VALIDATION m_kind = VALIDATION::ALWAYS_FAILS;

  //! True _iff_ CheckSchnorrSignature was actually called
  mutable bool m_was_called = false;

  SignatureCheckerMock() {}

  bool CheckSchnorrSignature(Span<const unsigned char> sig,
                             Span<const unsigned char> pubkey,
                             SigVersion sigversion,
                             ScriptExecutionData& execdata,
                             ScriptError* serror = nullptr) const override
  {
      m_was_called = true;
      switch (m_kind) {
      case VALIDATION::ALWAYS_SUCCEEDS:
          *serror = SCRIPT_ERR_OK;
          return true;
      case VALIDATION::ALWAYS_FAILS:
          *serror = SCRIPT_ERR_SCHNORR_SIG;
          return false;
      }
      __builtin_unreachable();
  }
};

} // anon namespace

BOOST_FIXTURE_TEST_SUITE(script_taproot_tests, BasicTestingSetup)

typedef std::vector<unsigned char> valtype;

/**
 * Testing EvalScript OP_CHECKSIGADD branch and EvalChecksigTapscript, both in
 * interpreter.cpp, against the BIP342 "Rules for signature opcodes".
 */
BOOST_AUTO_TEST_CASE(eval_checksigadd_basic_checks)
{
    static const valtype SIG_64BYTES(64, 0);  // N.B.: Must be () not {}!
    static const valtype SIG_65BYTES(65, 0);
    static const valtype SIG_EMPTY{};

    static const valtype PUBKEY_32BYTES(32, 0);
    static const valtype PUBKEY_15BYTES(15, 0);
    static const valtype PUBKEY_EMPTY{};

    static constexpr int64_t TEST_NUM = 10;

    static constexpr int64_t START_VALIDATION_WEIGHT{ 90 };
    static constexpr int64_t BIP342_SIGOPS_LIMIT{ 50 };
    static constexpr int64_t END_VALIDATION_WEIGHT{ START_VALIDATION_WEIGHT - BIP342_SIGOPS_LIMIT };

    /**
     * A fluent API for running these tests.
     *
     * (Easiest way to understand this class is to look at the actual tests
     * that follow in this function.)
     */
    struct Context
    {
        explicit Context(std::string_view descr) : testDescription(descr) {
            execdata.m_validation_weight_left_init = true;
            execdata.m_validation_weight_left = START_VALIDATION_WEIGHT;
        }

        std::string testDescription;
        SigVersion sigVersion = SigVersion::TAPSCRIPT;
        uint32_t flags = 0;
        CScript script;
        ScriptError err = SCRIPT_ERR_OK;
        std::vector<std::vector<unsigned char>> stack;
        ScriptExecutionData execdata;
        SignatureCheckerMock sigchecker;
        int64_t callerLine = 0;
        bool result = false;

        Context& SetVersion(SigVersion v)
        {
            sigVersion = v;
            return *this;
        }

        Context& SetChecker(SignatureCheckerMock::VALIDATION kind)
        {
            sigchecker.m_kind = kind;
            return *this;
        }

        Context& SetRemainingWeight(int64_t w)
        {
            execdata.m_validation_weight_left = w;
            return *this;
        }

        Context& AddFlags(uint32_t f)
        {
            flags |= f;
            return *this;
        }

        CScript& SetScript()
        {
            return script;
        }

        Context& DoTest(int64_t line)
        {
            callerLine = line;
            result = EvalScript(stack, script,
                                SCRIPT_VERIFY_TAPROOT | flags,
                                sigchecker,
                                sigVersion,
                                execdata,
                                &err);
            return *this;
        }

        Context& CheckCallSucceeded()
        {
            BOOST_CHECK_MESSAGE(result,
                               Descr()
                               << ": EvalScript succeeded, as expected");
            BOOST_CHECK_MESSAGE(err == SCRIPT_ERR_OK,
                                Descr()
                                << ": Error code expected OK, actual was "
                                << ScriptErrorString(err));
            return *this;
        }

        Context& CheckCallFailed(ScriptError expected)
        {
            BOOST_CHECK_MESSAGE(!result,
                               Descr()
                               << ": EvalScript failed, as expected");
            BOOST_CHECK_MESSAGE(err == expected,
                                Descr()
                                << ": Error code expected " << ScriptErrorString(expected)
                                << ", actual was " << ScriptErrorString(err));
            return *this;
        }

        Context& CheckSignatureWasValidated()
        {
            BOOST_CHECK_MESSAGE(sigchecker.m_was_called,
                               Descr()
                               << ": CheckSchnorrSignature was called, as expected");
            return *this;
        }

        Context& CheckSignatureWasNotValidated()
        {
            BOOST_CHECK_MESSAGE(!sigchecker.m_was_called,
                               Descr()
                               << ": CheckSchnorrSignature was not called, as expected");
            return *this;
        }

        Context& CheckRemainingValidationWeight(int64_t expected)
        {
            BOOST_CHECK_MESSAGE(execdata.m_validation_weight_left == expected,
                                Descr()
                                << ": Remaining validation weight expected "
                                << expected << ", actual was "
                                << execdata.m_validation_weight_left);
            return *this;
        }

        Context& CheckStackDepth(std::size_t expected)
        {
            BOOST_CHECK_MESSAGE(stack.size() == expected,
                                Descr()
                                << ": Stack depth expected " << expected
                                << ", actual was " << stack.size());
            return *this;
        }

        Context& CheckTOS(int64_t expected)
        {
            BOOST_CHECK_MESSAGE(!stack.empty(),
                                Descr()
                                << ": Stack expected at least one item, actually was empty");
            int64_t actual = CScriptNum(stack.at(0), false).GetInt64();
            BOOST_CHECK_MESSAGE(expected == actual,
                                Descr()
                                << ": Top-of-stack expected " << expected
                                << ", actual was " << actual);
            return *this;
        }

    private:
        std::string Descr() {
            std::string descr;
            descr.reserve(testDescription.size() + 20);
            descr += testDescription;
            descr += " (@";
            descr += std::to_string(callerLine);
            descr += ")";
            return descr;
        }
    };

    {
        Context ctx("SigVersion must not be BASE");
        ctx.SetVersion(SigVersion::BASE).SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_BAD_OPCODE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("SigVersion must not be WITNESS_V0");
        ctx.SetVersion(SigVersion::WITNESS_V0).SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_BAD_OPCODE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Minimum stack height 3 for OP_CHECKSIGADD");
        ctx.SetScript()
            << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_INVALID_STACK_OPERATION)
            .CheckStackDepth(2);
    }

    {
        Context ctx("`n` (2nd arg) size > 4 must fail");
        // This is probably meant to be a check on the _encoding_ - that it is
        // minimal, but it can also be a check on the _value_.  BIP342 doesn't
        // say which.  Could be both...
        ctx.SetScript()
            << SIG_EMPTY << CScriptNum(10000000000LL) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            // (IMO this is an _unsatisfactory_ error code to return for a required
            // BIP342 check, but see the `catch` clause in `EvalScript`)
            .CheckCallFailed(SCRIPT_ERR_UNKNOWN_ERROR)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Empty sig + empty pubkey");
        ctx.SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_EMPTY << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_PUBKEYTYPE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Sig + empty pubkey");
        ctx.SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_EMPTY << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_PUBKEYTYPE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Insufficient validation weight remaining");
        ctx.SetRemainingWeight(BIP342_SIGOPS_LIMIT-1)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_TAPSCRIPT_VALIDATION_WEIGHT)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Empty sig + 32byte pubkey skips validation");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasNotValidated()
            .CheckRemainingValidationWeight(START_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM);
    }

    {
        Context ctx("Empty sig + non32byte pubkey skips validation");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_15BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasNotValidated()
            .CheckRemainingValidationWeight(START_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM);
    }

    {
        Context ctx("non32byte pubkey ('unknown pubkey type') _with_ discourage flag fails");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .AddFlags(SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_PUBKEYTYPE)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_15BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_DISCOURAGE_UPGRADABLE_PUBKEYTYPE)
            .CheckSignatureWasNotValidated()
            .CheckStackDepth(3);
    }

    {
        Context ctx("32byte pubkey + sig with validation failure forced");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_FAILS)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_SCHNORR_SIG)
            .CheckSignatureWasValidated()
            .CheckStackDepth(3);
    }

    {
        Context ctx("32byte pubkey + sig with validation success forced");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasValidated()
            .CheckRemainingValidationWeight(END_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM+1);
    }

    {
        Context ctx("non32byte pubkey + empty sig with validation success forced");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_15BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasNotValidated()
            .CheckRemainingValidationWeight(START_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM);
    }
}


static bool HandleMissingData(MissingDataBehavior mdb)
{
    switch (mdb) {
        case MissingDataBehavior::ASSERT_FAIL:
            assert(!"missing data");
            break;
        case MissingDataBehavior::FAIL:
            return false;
    }
    assert(!"Unknown MissingDataBehavior value");
}

// `assert` statement signals SIGABRT - this macro succeeds iff that SIGABRT is
// raised. (Could be a false positive if code signals SIGABRT for _some other
// reason than calling `assert`; also if some _other_ `system_error` is
// caused ...)) (There doesn't appear to be any way to check the actual `assert`
// message to distinguish between different asserts, and the line number field
// of the exception is not set either.)
//
// TODO: Need to test this with MSVC++ - looking at the code in Boost's
// `execution_monitor.ipp` it looks to me like it handles the MSVC++ `assert`
// structured exception by reflecting it in the same way as Linux: via a
// `boost:execution_exception` with code `system_error`, but this needs to be
// verified.
#define BOOST_CHECK_SIGABRT(expr) \
{ \
    ::boost::execution_monitor exmon; \
    BOOST_CHECK_EXCEPTION( \
        exmon.vexecute([&](){(expr);}), \
        boost::execution_exception, \
        [](boost::execution_exception const& ex) \
            { return ex.code() == boost::execution_exception::system_error; } \
    ); \
}

BOOST_AUTO_TEST_CASE(handle_missing_data)
{
    // `HandleMissingData` is a static free function inside of `interpreter.cpp`.
    // Easiest way to get to it is via `SignatureHashSchnorr<CMutableTransaction>`
    // which takes an explicit `MissingDataBehavior` value which is what is
    // needed to exercise `HandleMissingData`.

    // N.B.: This is somewhat fragile.  We are just finding a path through
    // `SignatureHashSchnorr` that definitely gets to `HandleMissingData`. If
    // the code in `SignatureHashSchnorr` changes for whatever reason the
    // setup code below may not longer pick out that path.

    // Here we pick an acceptable SigVersion
    SigVersion sigversion = SigVersion::TAPROOT;

    // Here we pass the assert
    CMutableTransaction tx_to;
    tx_to.vin.push_back(CTxIn());
    uint32_t in_pos {0};

    // Here we take the `then` clause of the `if`
    PrecomputedTransactionData cache;
    cache.m_bip341_taproot_ready = false;
    cache.m_spent_outputs_ready = false;

    uint256 hash_out {0};
    ScriptExecutionData execdata;
    uint8_t hash_type {0};

    // `MissingDataBehavior::FAIL` simply returns false
    BOOST_CHECK(!SignatureHashSchnorr(hash_out, execdata, tx_to, in_pos,
                                      hash_type, sigversion, cache,
                                      MissingDataBehavior::FAIL));
    // Any other value for `MissingDataBehavior` triggers an `assert` function
    // which (on Linux) signals SIGABRT.
    BOOST_CHECK_SIGABRT(SignatureHashSchnorr(hash_out, execdata, tx_to, in_pos,
                                             hash_type, sigversion, cache,
                                             MissingDataBehavior::ASSERT_FAIL));
    BOOST_CHECK_SIGABRT(SignatureHashSchnorr(hash_out, execdata, tx_to, in_pos,
                                             hash_type, sigversion, cache,
                                             static_cast<MissingDataBehavior>(25)));
}

BOOST_AUTO_TEST_SUITE_END()
