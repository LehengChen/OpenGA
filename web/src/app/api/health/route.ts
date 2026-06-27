export const dynamic = 'force-dynamic'

export async function GET() {
  return Response.json({ status: 'ok', version: '0.3.0' })
}
