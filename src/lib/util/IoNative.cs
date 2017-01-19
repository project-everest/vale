using System.Numerics;

namespace Io_s {

public partial class HostConstants
{
    public static void NumCommandLineArgs(out BigInteger n)
    {
        n = new BigInteger(System.Environment.GetCommandLineArgs().Length);
    }

    public static void GetCommandLineArg(BigInteger i, out char[] arg)
    {
        arg = System.Environment.GetCommandLineArgs()[(uint)i].ToCharArray();
    }
}

}
