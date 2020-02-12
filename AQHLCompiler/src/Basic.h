#pragma once

#include <stdint.h>
#include <assert.h>
#include <cstring>
#include <mutex>
#include <Windows.h>
#include <Shlwapi.h>
#include <stdlib.h>
#include <iostream>
#include <initializer_list>
#include <thread>
#include <fstream>
#include <sstream>
#include <atomic>
#include <algorithm>
#include <immintrin.h>


#ifdef PROFILE
#define CONCAT2(x, y) x##y
#define CONCAT(x, y) CONCAT2(x, y)
#define PROFILE_FUNC()                 Timer CONCAT(timer,__LINE__)(__FUNCTION__)
#define PROFILE_FUNC_DATA(data)        Timer CONCAT(timer,__LINE__)(__FUNCTION__, data)
#define PROFILE_ZONE(name)             Timer CONCAT(timer,__LINE__)(name)
#define PROFILE_ZONE_DATA(name, data)  Timer CONCAT(timer,__LINE__)(name, data)
#define PROFILE_START(name)			   startProfile(name)
#define PROFILE_START_DATA(name, data) startProfile(name, data)
#define PROFILE_END()                  endProfile()
#else
#define PROFILE_FUNC()
#define PROFILE_FUNC_DATA(data)
#define PROFILE_ZONE(name)
#define PROFILE_ZONE_DATA(name, data)
#define PROFILE_START(name)
#define PROFILE_START_DATA(name, data)
#define PROFILE_END()
#endif



#undef small
#undef min
#undef max
#undef CONST

using Scope_Lock = std::lock_guard<std::mutex>;


typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t s8;
typedef int16_t s16;
typedef int32_t s32;
typedef int64_t s64;

typedef uintptr_t ptr;

typedef u16 ulang;
typedef s16 slang;

#define ULANG_MAX 65535 // @WordSize
#define ULANG_MIN 0

#define SLANG_MAX 32767 // @WordSize
#define SLANG_MIN (-32768) // @WordSize

#define BITS_IN_LANG_SIZE 16 // @WordSize

#define my_min(a, b) ((a) < (b) ? (a) : (b))
#define my_max(a, b) ((a) > (b) ? (a) : (b))

struct CodeLocation {
	u32 line;
	u32 column;
	u32 fileUid;
};

struct EndLocation {
	u32 line;
	u32 column;

	EndLocation() {}
	EndLocation(const CodeLocation &code) : line(code.line), column(code.column) {}
};


const char *getFilename(u32 fileUid);

inline std::ostream &operator<<(std::ostream &out, const CodeLocation &location) {
	return out << getFilename(location.fileUid) << ':' << location.line << ',' << location.column;
}

#if PROFILE
struct Profile {
	const char *name = 0;
	const char *data = 0;
	u64 time;
	s32 threadId;
};

extern Profile profiles[10000000];
extern std::atomic_uint32_t profileIndex;

struct Timer {

	Timer(const char *name) {
		u32 write = profileIndex++;

		profiles[write].name = name;
		
		QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&profiles[write].time));
		
		profiles[write].threadId = *reinterpret_cast<s32 *>(reinterpret_cast<u8 *>(__readgsqword(0x30)) + 0x48);
	}

	Timer(const char *name, const char* data) {
		u32 write = profileIndex++;

		profiles[write].name = name;
		profiles[write].data = data;
		
		QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&profiles[write].time));
		
		profiles[write].threadId = *reinterpret_cast<s32 *>(reinterpret_cast<u8 *>(__readgsqword(0x30)) + 0x48);
	}

	~Timer() {
		u32 write = profileIndex++;

		
		QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&profiles[write].time));
		
		profiles[write].threadId = *reinterpret_cast<s32 *>(reinterpret_cast<u8 *>(__readgsqword(0x30)) + 0x48);
	}
};

inline void startProfile(const char *name) {
	u32 write = profileIndex++;

	profiles[write].name = name;
	
	QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&profiles[write].time));
	
	profiles[write].threadId = *reinterpret_cast<s32 *>(reinterpret_cast<u8 *>(__readgsqword(0x30)) + 0x48);
}

inline void startProfile(const char *name, const char *data) {
	u32 write = profileIndex++;

	profiles[write].name = name;
	profiles[write].data = data;
	
	QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&profiles[write].time));
	
	profiles[write].threadId = *reinterpret_cast<s32 *>(reinterpret_cast<u8 *>(__readgsqword(0x30)) + 0x48);
}

inline void endProfile() {
	u32 write = profileIndex++;

	
	QueryPerformanceCounter(reinterpret_cast<LARGE_INTEGER *>(&profiles[write].time));
	
	profiles[write].threadId = *reinterpret_cast<s32 *>(reinterpret_cast<u8 *>(__readgsqword(0x30)) + 0x48);
}

#endif