#include "Basic.h"
#include "BlockWriter.h"

#include "CompilerMain.h"

WorkQueue<WriteJob> blockWriterQueue;

void runBlockWriter() {
	PROFILE_FUNC();

	DWORD written;

	HANDLE file = CreateFileA(output, fileMap ? GENERIC_WRITE | GENERIC_READ : GENERIC_WRITE, 0, 0, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, 0); // @Platform
	HANDLE map = INVALID_HANDLE_VALUE;

	if (file == INVALID_HANDLE_VALUE) {
		reportError("Could not open output file");
	}
	else if (fileMap) {
		map = CreateFileMappingA(file, 0, PAGE_READWRITE, 0, (ULANG_MAX + 1) * sizeof(ulang), 0);
		DWORD err = GetLastError();
	}

	void *view = nullptr;

	if (fileMap) {
		if (map != INVALID_HANDLE_VALUE) {
			view = MapViewOfFile(map, FILE_MAP_WRITE, 0, 0, 0);
		}
	}

	while (true) {
		WriteJob write = blockWriterQueue.take();

		if (!write.values) break;

		PROFILE_ZONE("Write block");

		if (fileMap) {
			if (view) {
				memcpy((char *) view + sizeof(ulang) * write.offset, write.values, sizeof(ulang) * write.count);
			}
		}
		else {
			if (file != INVALID_HANDLE_VALUE) {
				LARGE_INTEGER writeIndex;
				writeIndex.QuadPart = write.offset * sizeof(ulang);
				LARGE_INTEGER newIndex;

				SetFilePointerEx(file, writeIndex, &newIndex, FILE_BEGIN);
				WriteFile(file, write.values, sizeof(ulang) * write.count, &written, 0);
			}
		}
	}

	if (view) {
		UnmapViewOfFile(view);
	}

	if (map != INVALID_HANDLE_VALUE) {
		CloseHandle(map);
	}

	if (file != INVALID_HANDLE_VALUE) {
		PROFILE_ZONE("Close File");
		CloseHandle(file);
	}
}
