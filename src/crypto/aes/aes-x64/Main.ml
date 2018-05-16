let _ = CmdLineParser.parse_cmdline [("aes_key_expansion",  X64_AES.va_code_KeyExpansionStdcall); ("gcm_encrypt", X64_GCMopt.va_code_gcm_stdcall)]
